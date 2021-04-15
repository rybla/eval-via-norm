{-
# lam: the simply-typed lambda calculus

inspired by: https://github.com/jeprinz/unquote-n/blob/main/STLC/NbE.agda)

vocab:

- _base_ language:
         the language (here, agda) used for implementing the
         normalizer for the interpreted language.

- _interpreted_ language:
         the language language that the normalizer normalizes
         terms of.

- _semantic_ language:
         the subset of the base language that reflects terms 
         in the interpreted language.
-}


open import Relation.Binary.PropositionalEquality

infixr 10 _`→_

infix  18 `_ s_
infixr 17 `neu_
infixl 16 _`∙_ 
infixr 15 `λ_

infixr 11 _,_
infixr 10 _⇉_ _↦_ _∘_ _∘′_


{-
## Interpreted Language

-}

-- interpreted type
data Type : Set where
  _`→_ : Type → Type → Type
  `●   : Type

-- interpreted context
data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

-- interpreted variable
data Var : (Γ : Ctx) → Type → Set where
  z  : ∀ {Γ α}   → Var (Γ , α) α
  s_ : ∀ {Γ α β} → Var Γ      α → Var (Γ , β) α

-- interpreted expression
data Exp : Ctx → Type → Set where
  `_   : ∀ {Γ α}   → (x : Var Γ α) → Exp Γ α
  `●   : ∀ {Γ}     → Exp Γ `●
  `λ_  : ∀ {Γ α β} → Exp (Γ , α) β  → Exp Γ (α `→ β)
  _`∙_ : ∀ {Γ α β} → Exp Γ (α `→ β) → Exp Γ α → Exp Γ β


{-
## Interpreted Neutral and Normal Forms

-}

data Neu : Ctx → Type → Set
data Nrm : Ctx → Type → Set

-- interpreted neutral form
data Neu where
  `_   : ∀ {Γ α}   → (x : Var Γ α)  → Neu Γ α
  _`∙_ : ∀ {Γ α β} → Neu Γ (α `→ β) → Nrm Γ α → Neu Γ β

-- interpreted normal form
data Nrm where
  `●    : ∀ {Γ}     → Nrm Γ `●
  `λ_   : ∀ {Γ α β} → Nrm (Γ , α) β → Nrm Γ (α `→ β)
  `neu_ : ∀ {Γ α}   → Neu Γ       α → Nrm Γ α


{-
## Renaming of Interpreted Contexts
-}

-- type of renamings from Γ₁ to Γ₂
_⇉_ : Ctx → Ctx → Set 
Γ₁ ⇉ Γ₂ = ∀ {α} → Var Γ₁ α → Var Γ₂ α

-- composition of renamings
_∘_ : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⇉ Γ₂) → (Γ₂ ⇉ Γ₃) → (Γ₁ ⇉ Γ₃)
σ ∘ σ′ = λ x → σ′ (σ x)

-- renaming that weakens context by introducing 1 var
weaken1 : ∀ {Γ α} → (Γ ⇉ Γ , α)
weaken1 ρ = s ρ

-- renaming that forgets 1 var from given renaming
forget1 : ∀ {Γ₁ Γ₂ α} → (Γ₁ , α ⇉ Γ₂) → (Γ₁ ⇉ Γ₂)
forget1 ρ x = ρ (s x)

-- the identity renaming
ρ-id : ∀ {Γ} → (Γ ⇉ Γ)
ρ-id x = x


{-
## Semantic Language

-}

-- types of semantic expressions

Sem  : Ctx → Type → Set
Sem′ : Ctx → Type → Set

Sem Γ (α `→ β) = Sem′ Γ α → Sem Γ β
Sem Γ `●       = Nrm Γ `●

Sem′ Γ α = ∀ {Γ′} → Γ ⇉ Γ′ → Sem Γ′ α


{-
## Substitution of Interpreted Contexts

-}

-- type of substitutions from Γ₁ to Γ₂
_↦_ : Ctx → Ctx → Set
Γ₁ ↦ Γ₂ = ∀ {α} → Var Γ₁ α → Sem′ Γ₂ α

-- (defined in next section)
apply : ∀ {Γ α} → Neu Γ α → Sem Γ α
reify : ∀ {Γ α} → Sem′ Γ α → Nrm Γ α

-- the identity substitution
σ-id : ∀ {Γ} → (Γ ↦ Γ)
σ-id x ρ = apply (` ρ x)

-- composition of substitution and renaming
_∘′_ : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ↦ Γ₂) → (Γ₂ ⇉ Γ₃) → (Γ₁ ↦ Γ₃)
σ ∘′ ρ = λ x ρ′ → σ x (ρ ∘ ρ′)


{-
## Evaluation and Normalization

-}

-- application of interpreted neutral form as semantic expression
apply {_} {α `→ β} a = λ g → apply (a `∙ reify g)
apply {_} {`●}     a = `neu a

-- reification of semantic expression as interpreted normal form
reify {_} {α `→ β} g = `λ reify λ ρ_ → g (forget1 ρ_) λ ρ′_ → apply (` ρ′ ρ z)
reify {_} {`●}     g = g ρ-id

-- substitution that appends one var,
-- corresponding to given semantic expression,
-- to given substitution
append1 : ∀ {Γ₁ Γ₂ α} → (Γ₁ ↦ Γ₂) → Sem′ Γ₂ α → (Γ₁ , α ↦ Γ₂)
append1 σ a z     ρ = a ρ
append1 σ a (s x) ρ = σ x ρ

-- evaluation of interpreted expression as semantic expression
eval : ∀ {Γ₁ Γ₂ α} → Exp Γ₁ α → Γ₁ ↦ Γ₂ → Sem Γ₂ α
eval (` x)    σ = σ x ρ-id
eval (`λ a)   σ = λ g → eval a (append1 σ g)
eval (f `∙ a) σ = eval f σ λ ρ → eval a (σ ∘′ ρ)
eval `●       σ = `●

-- normalization of interpreted expression as interpreted normal form
-- "normalize = reify ∘ evaluate"
norm : ∀ {Γ α} → Exp Γ α → Nrm Γ α
norm a = reify λ ρ → eval a (σ-id ∘′ ρ)


{-
## Examples
-}

_ : norm {∅} {`●} ((`λ ` z) `∙ `●) ≡ `●
_ = refl

_ : norm {∅} {`●} ((`λ ` z `∙ `●) `∙ (`λ ` z)) ≡ `●
_ = refl

_ : norm {∅} {`● `→ `●} (`λ (`λ ` z) `∙ `●) ≡ `λ `●
_ = refl

_ : norm {∅} {`● `→ `●} (`λ ((`λ ` z) `∙ ` z)) ≡ `λ (`neu ` z)
_ = refl

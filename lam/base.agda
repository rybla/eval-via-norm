{-
lam: the simply-typed lambda calculus

inspired by https://github.com/jeprinz/unquote-n/blob/main/STLC/NbE.agda
-}

open import Relation.Binary.PropositionalEquality

infixr 10 _`→_

infixr 17 `_ s_
infixl 16 _`∙_
infixr 15 `λ_

infixr 11 _,_
infixr 10 _⇉_ _↦_ _∘_ _∘′_

-- type
data Type : Set where
  _`→_ : Type → Type → Type
  `●   : Type

-- context
data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

-- variable
data Var : (Γ : Ctx) → Type → Set where
  z : ∀ {Γ α}   → Var (Γ , α) α
  s_ : ∀ {Γ α β} → Var Γ      α → Var (Γ , β) α

-- expression
data Exp : Ctx → Type → Set where
  `_   : ∀ {Γ α}   → (x : Var Γ α)  → Exp Γ α
  `λ_  : ∀ {Γ α β} → Exp (Γ , α) β  → Exp Γ (α `→ β)
  _`∙_ : ∀ {Γ α β} → Exp Γ (α `→ β) → Exp Γ α → Exp Γ β
  `●   : ∀ {Γ}     → Exp Γ `●

--
-- neutral and normal forms
--

data Neu : Ctx → Type → Set
data Nrm : Ctx → Type → Set

-- neutral form
data Neu where
  `_   : ∀ {Γ α}   → (x : Var Γ α)  → Neu Γ α
  _`∙_ : ∀ {Γ α β} → Neu Γ (α `→ β) → Nrm Γ α → Neu Γ β

-- normal form
data Nrm where
  `λ_ : ∀ {Γ α β} → Nrm (Γ , α) β → Nrm Γ (α `→ β)
  `neu : ∀ {Γ α}  → Neu Γ       α → Nrm Γ α
  `●  : ∀ {Γ}     → Nrm Γ `●

--
-- renaming
--

-- renaming
_⇉_ : Ctx → Ctx → Set 
Γ₁ ⇉ Γ₂ = ∀ {α} → Var Γ₁ α → Var Γ₂ α

-- compose renamings
_∘_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ⇉ Γ₂ → Γ₂ ⇉ Γ₃ → Γ₁ ⇉ Γ₃
σ ∘ σ′ = λ x → σ′ (σ x)

-- convenient renamings

weaken1 : ∀ {Γ α} → Γ ⇉ (Γ , α)
weaken1 ρ = s ρ

forget1 : ∀ {Γ₁ Γ₂ α} → Γ₁ , α ⇉ Γ₂ → Γ₁ ⇉ Γ₂
forget1 ρ x = ρ (s x)

ρ-id : ∀ {Γ} → Γ ⇉ Γ
ρ-id x = x

--
-- semantic domain
--

Sem  : Ctx → Type → Set
Sem′ : Ctx → Type → Set

Sem Γ (α `→ β) = Sem′ Γ α → Sem Γ β
Sem Γ `●       = Nrm Γ `●

Sem′ Γ α = ∀ {Γ′} → Γ ⇉ Γ′ → Sem Γ′ α

--
-- substitution
--

-- substitution
_↦_ : Ctx → Ctx → Set
Γ₁ ↦ Γ₂ = ∀ {α} → Var Γ₁ α → Sem′ Γ₂ α

apply : ∀ {Γ α} → Neu Γ α → Sem Γ α
reify : ∀ {Γ α} → Sem′ Γ α → Nrm Γ α

apply {_} {α `→ β} a = λ g → apply (a `∙ reify g)
apply {_} {`●}     a = `neu a

reify {_} {α `→ β} g = `λ reify (λ ρ_ → g (forget1 ρ_) (λ ρ′_ → apply (` ρ′ ρ z)))
reify {_} {`●}     g = g ρ-id

lift : ∀ {Γ₁ Γ₂ α} → Γ₁ ↦ Γ₂ → Γ₁ , α ↦ Γ₂ , α
lift σ z     ρ = apply (` ρ z)
lift σ (s x) ρ = σ x (forget1 ρ)

σ-id : ∀ {Γ} → Γ ↦ Γ
σ-id x ρ = apply (` ρ x)

_∘′_ : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ↦ Γ₂ → Γ₂ ⇉ Γ₃ → Γ₁ ↦ Γ₃
σ ∘′ ρ = λ x ρ′ → σ x (ρ ∘ ρ′)

append1 : ∀ {Γ₁ Γ₂ α} → Γ₁ ↦ Γ₂ → Sem′ Γ₂ α → Γ₁ , α ↦ Γ₂
append1 σ a z     ρ = a ρ
append1 σ a (s x) ρ = σ x ρ

eval : ∀ {Γ₁ Γ₂ α} → Exp Γ₁ α → Γ₁ ↦ Γ₂ → Sem Γ₂ α
eval (` x)    σ = σ x ρ-id
eval (`λ a)   σ = λ g → eval a (append1 σ g)
eval (f `∙ a) σ = eval f σ λ ρ → eval a (σ ∘′ ρ)
eval `●       σ = `●

-- "norm = reify ∘ eval"
norm : ∀ {Γ α} → Exp Γ α → Nrm Γ α
norm a = reify (λ ρ → eval a (σ-id ∘′ ρ))

--
-- examples
--

_ : norm {∅} {`●} ((`λ ` z) `∙ `●) ≡ `●
_ = refl

_ : norm {∅} {`●} ((`λ ` z `∙ `●) `∙ (`λ ` z)) ≡ `●
_ = refl

_ : norm {∅} {`● `→ `●} (`λ (`λ ` z) `∙ `●) ≡ `λ `●
_ = refl

_ : norm {∅} {`● `→ `●} (`λ ((`λ ` z) `∙ ` z)) ≡ `λ (`neu (` z))
_ = refl

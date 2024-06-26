import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

module stlc-ccc where

module stlc where

infix 4 _≡βη_
infixr 7 _⇒_
infixl 8 _*_
infixl 5 _•_
infix 4 _∋_
infix 5 ƛ_
infix 8 _[_]
infixl 7 _·_
infixl 5 _ₛ∘ₑ_

data Ty : Set where
  unit : Ty
  _*_ : Ty → Ty → Ty
  _⇒_ : Ty → Ty → Ty

variable A B C : Ty

data Cx : Set where
  ∅ : Cx
  _•_ : Cx → Ty → Cx

variable Γ Γ′ Δ Ξ Θ : Cx

data _∋_ : Cx → Ty → Set where
  zero : Γ • A ∋ A
  suc : Γ ∋ A → Γ • B ∋ A

data Tm : Cx → Ty → Set where
  tt : Tm Γ unit
  <_,_> : Tm Γ A → Tm Γ B → Tm Γ (A * B)
  fst : Tm Γ (A * B) → Tm Γ A
  snd : Tm Γ (A * B) → Tm Γ B
  ƛ_ : Tm (Γ • A) B → Tm Γ (A ⇒ B)
  _·_ : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  var : Γ ∋ A → Tm Γ A

variable
  a a′ a″ : Tm Γ A
  b b′ b″ : Tm Γ B
  p p′ p″ : Tm Γ (A * B)
  f f′ f″ : Tm Γ (A ⇒ B)

data OPE : Cx → Cx → Set where
  ∅ : OPE ∅ ∅
  drop : OPE Γ Δ → OPE (Γ • A) Δ
  keep : OPE Γ Δ → OPE (Γ • A) (Δ • A)

variable ε ε₁ ε₂ ε₃ φ : OPE Δ Γ

idₑ : OPE Γ Γ
idₑ {∅} = ∅
idₑ {Γ • A} = keep idₑ

↑ : OPE (Γ • A) Γ
↑ = drop idₑ

_∘ₑ_ : OPE Δ Γ → OPE Ξ Δ → OPE Ξ Γ
ε ∘ₑ ∅ = ε
ε ∘ₑ drop φ = drop (ε ∘ₑ φ)
drop ε ∘ₑ keep φ = drop (ε ∘ₑ φ)
keep ε ∘ₑ keep φ = keep (ε ∘ₑ φ)

embed-var : Γ ∋ A → OPE Δ Γ → Δ ∋ A
embed-var x (drop ε) = suc (embed-var x ε)
embed-var zero (keep ε) = zero
embed-var (suc x) (keep ε) = suc (embed-var x ε)

embed : Tm Γ A → OPE Δ Γ → Tm Δ A
embed tt ε = tt
embed < a , b > ε = < embed a ε , embed b ε >
embed (fst p) ε = fst (embed p ε)
embed (snd p) ε = snd (embed p ε)
embed (ƛ b) ε = ƛ embed b (keep ε)
embed (f · a) ε = embed f ε · embed a ε
embed (var x) ε = var (embed-var x ε)

data Sb : Cx → Cx → Set where
  ∅ : Sb Γ ∅
  _•_ : Sb Δ Γ → Tm Δ A → Sb Δ (Γ • A)

variable σ τ : Sb Δ Γ

_ₛ∘ₑ_ : Sb Δ Γ → OPE Ξ Δ → Sb Ξ Γ
∅ ₛ∘ₑ _ = ∅
(σ • a) ₛ∘ₑ ε = (σ ₛ∘ₑ ε) • embed a ε

⌜drop⌝ : Sb Δ Γ → Sb (Δ • A) Γ
⌜drop⌝ σ = σ ₛ∘ₑ ↑

⌜keep⌝ : Sb Δ Γ → Sb (Δ • A) (Γ • A)
⌜keep⌝ σ = ⌜drop⌝ σ • var zero

idₛ : Sb Γ Γ
idₛ {∅} = ∅
idₛ {Γ • A} = ⌜keep⌝ idₛ

⌜_⌝ : OPE Δ Γ → Sb Δ Γ
⌜ ∅ ⌝ = ∅
⌜ drop ε ⌝ = ⌜drop⌝ ⌜ ε ⌝
⌜ keep ε ⌝ = ⌜keep⌝ ⌜ ε ⌝

_⟪_⟫ : Γ ∋ A → Sb Δ Γ → Tm Δ A
zero ⟪ σ • a ⟫ = a
(suc x) ⟪ σ • a ⟫ = x ⟪ σ ⟫

_[_] : Tm Γ A → Sb Δ Γ → Tm Δ A
tt [ σ ] = tt
< a , b > [ σ ] = < a [ σ ] , b [ σ ] >
fst p [ σ ] = fst (p [ σ ])
snd p [ σ ] = snd (p [ σ ])
(ƛ b) [ σ ] = ƛ b [ ⌜keep⌝ σ ]
(f · a) [ σ ] = f [ σ ] · a [ σ ]
var x [ σ ] = x ⟪ σ ⟫

_∘ₛ_ : Sb Δ Γ → Sb Ξ Δ → Sb Ξ Γ
∅ ∘ₛ τ = ∅
(σ • a) ∘ₛ τ = (σ ∘ₛ τ) • a [ τ ]

data _≡βη_ : Tm Γ A → Tm Γ A → Set where
  β : (ƛ b) · a ≡βη b [ idₛ • a ]

  η : f ≡βη ƛ embed f ↑ · var zero

  β-fst : fst < a , b > ≡βη a

  β-snd : snd < a , b > ≡βη b

  η-pair : p ≡βη < fst p , snd p >

  tt-uniq : a ≡βη tt

  cong-ƛ : b ≡βη b′ → ƛ b ≡βη ƛ b′

  cong-app : f ≡βη f′ → a ≡βη a′ → f · a ≡βη f′ · a′

  cong-fst : p ≡βη p′ → fst p ≡βη fst p′

  cong-snd : p ≡βη p′ → snd p ≡βη snd p′

  cong-pair : a ≡βη a′ → b ≡βη b′ → < a , b > ≡βη < a′ , b′ >

  refl : a ≡βη a

  sym : a ≡βη a′ → a′ ≡βη a

  trans : a ≡βη a′ → a′ ≡βη a″ → a ≡βη a″

open stlc

module lemmas where
  embed-var-idₑ-identity : ∀ (x : Γ ∋ A) → embed-var x idₑ ≡ x
  embed-var-idₑ-identity zero = refl
  embed-var-idₑ-identity (suc x)
    rewrite embed-var-idₑ-identity x = refl

  commute-⟪ₛ∘ₑ⟫ : ∀ (σ : Sb Δ Γ) (ε : OPE Ξ Δ) (x : Γ ∋ A)
              → x ⟪ σ ₛ∘ₑ ε ⟫ ≡ embed (x ⟪ σ ⟫) ε
  commute-⟪ₛ∘ₑ⟫ (σ • a) ε zero = refl
  commute-⟪ₛ∘ₑ⟫ (σ • a) ε (suc x) = commute-⟪ₛ∘ₑ⟫ σ ε x

  ⟪idₛ⟫-identity : ∀ (x : Γ ∋ A) → x ⟪ idₛ ⟫ ≡ var x
  ⟪idₛ⟫-identity zero = refl
  ⟪idₛ⟫-identity (suc {B = B} x)
    rewrite commute-⟪ₛ∘ₑ⟫ idₛ (↑ {_} {B}) x
          | ⟪idₛ⟫-identity x
          | embed-var-idₑ-identity x      = refl

open lemmas

record Category : Set₁ where
  infixl 5 _∘_
  infixr 7 _⟶_

  field
    Ob : Set
    _⟶_ : Ob → Ob → Set

    _∘_ : ∀ {A B C} → B ⟶ C → A ⟶ B → A ⟶ C
    id : ∀ {A} → A ⟶ A

    ∘/assoc : ∀ {A B C D} (f : C ⟶ D) (g : B ⟶ C) (h : A ⟶ B)
            → f ∘ g ∘ h ≡ f ∘ (g ∘ h)

    ∘/identityˡ : ∀ {A B} (f : A ⟶ B)
                → id ∘ f ≡ f

    ∘/identityʳ : ∀ {A B} (f : A ⟶ B)
                → f ∘ id ≡ f

record Product (𝒞 : Category) : Set where
  infix 8 _⋆_ _⋆⋆_
  open Category 𝒞
  field
    _⋆_ : Ob → Ob → Ob
    ⟨_,_⟩ : ∀ {X Y Z} → X ⟶ Y → X ⟶ Z → X ⟶ Y ⋆ Z
    π₁ : ∀ {X Y} → X ⋆ Y ⟶ X
    π₂ : ∀ {X Y} → X ⋆ Y ⟶ Y

    π₁/proj : ∀ {X Y Z} → (f : X ⟶ Y) (g : X ⟶ Z) → π₁ ∘ ⟨ f , g ⟩ ≡ f
    π₂/proj : ∀ {X Y Z} → (f : X ⟶ Y) (g : X ⟶ Z) → π₂ ∘ ⟨ f , g ⟩ ≡ g
    ⋆/uniq : ∀ {X Y Z} → (h : X ⟶ Y ⋆ Z) → h ≡ ⟨ π₁ ∘ h , π₂ ∘ h ⟩

  _⋆⋆_ : ∀ {A B C D : Ob} → A ⟶ B → C ⟶ D → A ⋆ C ⟶ B ⋆ D
  f ⋆⋆ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  ⋆-∘-dist : ∀ {X Y Z W} (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X)
            → ⟨ f , g ⟩ ∘ h ≡ ⟨ f ∘ h , g ∘ h ⟩
  ⋆-∘-dist f g h
    rewrite ⋆/uniq (⟨ f , g ⟩ ∘ h)
          | Eq.sym (∘/assoc π₁ ⟨ f , g ⟩ h)
          | π₁/proj f g
          | Eq.sym (∘/assoc π₂ ⟨ f , g ⟩ h)
          | π₂/proj f g                     = refl

  ⋆⋆-∘-dist : ∀ {A B C X Y Z}
               (f : B ⟶ C) (g : A ⟶ B) (h : Y ⟶ Z) (k : X ⟶ Y)
           → f ⋆⋆ h ∘ g ⋆⋆ k ≡ (f ∘ g) ⋆⋆ (h ∘ k)
  ⋆⋆-∘-dist {A = A} {X = X} f g h k
    rewrite ⋆-∘-dist (f ∘ π₁) (h ∘ π₂) (g ⋆⋆ k)
          | ∘/assoc f π₁ ⟨ g ∘ π₁ , k ∘ π₂ ⟩
          | π₁/proj (g ∘ π₁) (k ∘ π₂)
          | ∘/assoc h π₂ ⟨ g ∘ π₁ , k ∘ π₂ ⟩
          | π₂/proj (g ∘ π₁) (k ∘ π₂)
          | ∘/assoc f g (π₁ {_} {X})
          | ∘/assoc h k (π₂ {A})                = refl

  ⋆-expand : ∀ {X Y Z} (f : X ⟶ Y) (g : X ⟶ Z)
           → ⟨ f , g ⟩ ≡ (f ⋆⋆ id) ∘ ⟨ id , g ⟩
  ⋆-expand {X} {Y} {Z} f g
    rewrite ⋆-∘-dist (f ∘ π₁) (id ∘ π₂) ⟨ id , g ⟩
          | ∘/assoc f π₁ ⟨ id , g ⟩
          | ∘/assoc id π₂ ⟨ id , g ⟩
          | π₁/proj id g
          | π₂/proj id g
          | ∘/identityʳ f
          | ∘/identityˡ g                          = refl

record CartesianClosed (𝒞 : Category) : Set₁ where
  open Category 𝒞

  field
    prod : Product 𝒞
  open Product prod

  field
    𝟙 : Ob
    ! : ∀ {A} → A ⟶ 𝟙

    !/uniq : ∀ {A} (h : A ⟶ 𝟙) → h ≡ !


    _^_ : Ob → Ob → Ob

    curry : ∀ {A B X} → A ⋆ B ⟶ X → A ⟶ X ^ B
    eval : ∀ {X B} → (X ^ B) ⋆ B ⟶ X

    eval/curry : ∀ {A B X} (f : A ⋆ B ⟶ X) → eval ∘ (curry f ⋆⋆ id) ≡ f
    curry/uniq : ∀ {A B X} → (g : A ⟶ X ^ B) → curry (eval ∘ (g ⋆⋆ id)) ≡ g

  curry/subst : ∀ {A B X Y} (f : A ⋆ B ⟶ X) (g : Y ⟶ A)
              → curry (f ∘ (g ⋆⋆ id)) ≡ curry f ∘ g
  curry/subst f g =
    begin
      curry (f ∘ (g ⋆⋆ id))
    ≡⟨ Eq.cong curry (
      begin
        f ∘ (g ⋆⋆ id)
      ≡⟨ Eq.cong (_∘ (g ⋆⋆ id)) (Eq.sym (eval/curry f)) ⟩
        eval ∘ (curry f ⋆⋆ id) ∘ (g ⋆⋆ id)
      ≡⟨ ∘/assoc eval (curry f ⋆⋆ id) (g ⋆⋆ id) ⟩
        eval ∘ ((curry f ⋆⋆ id) ∘ (g ⋆⋆ id))
      ≡⟨ Eq.cong (eval ∘_) (⋆⋆-∘-dist (curry f) g id id) ⟩
        eval ∘ ((curry f ∘ g) ⋆⋆ (id ∘ id))
      ≡⟨ Eq.cong (eval ∘_) (Eq.cong ((curry f ∘ g) ⋆⋆_) (∘/identityʳ id)) ⟩
        eval ∘ ((curry f ∘ g) ⋆⋆ id)
      ∎
    )⟩
      curry (eval ∘ ((curry f ∘ g) ⋆⋆ id))
    ≡⟨ curry/uniq (curry f ∘ g) ⟩
      curry f ∘ g
    ∎

module Semantics (𝒞 : Category) (ccc : CartesianClosed 𝒞) where
  open Category 𝒞
  open CartesianClosed ccc
  open Product prod

  infix 4 _~_
  infix 4 _∼_

  record Interpretation (X : Set) : Set where
    field
      ⟦_⟧ : X → Ob

  open Interpretation ⦃...⦄ public

  instance
    ⟦Ty⟧ : Interpretation Ty
    Interpretation.⟦ ⟦Ty⟧ ⟧ unit = 𝟙
    Interpretation.⟦ ⟦Ty⟧ ⟧ (A * B) = ⟦ A ⟧ ⋆ ⟦ B ⟧
    Interpretation.⟦ ⟦Ty⟧ ⟧ (A ⇒ B) = ⟦ B ⟧ ^ ⟦ A ⟧

    ⟦Cx⟧ : Interpretation Cx
    Interpretation.⟦ ⟦Cx⟧ ⟧ ∅ = 𝟙
    Interpretation.⟦ ⟦Cx⟧ ⟧ (Γ • A) = ⟦ Γ ⟧ ⋆ ⟦ A ⟧

  variable
    γ : ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧
    δ : ⟦ Ξ ⟧ ⟶ ⟦ Δ ⟧
    𝑎 : ⟦ Γ ⟧ ⟶ ⟦ A ⟧
    𝑏 : ⟦ Γ ⟧ ⟶ ⟦ B ⟧
    𝑐 : ⟦ Γ ⟧ ⟶ ⟦ C ⟧
    𝑝 : ⟦ Γ ⟧ ⟶ ⟦ A * B ⟧
    𝑓 : ⟦ Γ ⟧ ⟶ ⟦ A ⇒ B ⟧

  ⟦var⟧ : Γ ∋ A → ⟦ Γ ⟧ ⟶ ⟦ A ⟧
  ⟦var⟧ zero = π₂
  ⟦var⟧ (suc x) = ⟦var⟧ x ∘ π₁

  ℰ⟦_⟧ : Tm Γ A → ⟦ Γ ⟧ ⟶ ⟦ A ⟧
  ℰ⟦ tt ⟧ = !
  ℰ⟦ < a , b > ⟧ = ⟨ ℰ⟦ a ⟧ , ℰ⟦ b ⟧ ⟩
  ℰ⟦ fst p ⟧ = π₁ ∘ ℰ⟦ p ⟧
  ℰ⟦ snd p ⟧ = π₂ ∘ ℰ⟦ p ⟧
  ℰ⟦ ƛ b ⟧ = curry ℰ⟦ b ⟧
  ℰ⟦ f · a ⟧ = eval ∘ ⟨ ℰ⟦ f ⟧ , ℰ⟦ a ⟧ ⟩
  ℰ⟦ var x ⟧ = ⟦var⟧ x

  _~_ : OPE Δ Γ → ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧ → Set
  _~_ {_} {Γ} ε γ =
    ∀ {A} (x : Γ ∋ A) → ⟦var⟧ (embed-var x ε) ≡ ⟦var⟧ x ∘ γ

  ↑~π₁ : ∀ {Γ A} → ↑ {Γ} {A} ~ π₁
  ↑~π₁ zero = refl
  ↑~π₁ {Γ • B} {A} (suc x) rewrite ↑~π₁ {Γ} {B} x = refl

  ~-ext : ∀ {ε : OPE Δ Γ} {γ : ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧}
          (A : Ty)
        → ε ~ γ
        → keep {A = A} ε ~ γ ⋆⋆ id {⟦ A ⟧}
  ~-ext {Δ = Δ} {γ = γ} A pf zero
    rewrite π₂/proj (γ ∘ π₁) (id {⟦ A ⟧} ∘ π₂)
          | ∘/identityˡ (π₂ {⟦ Δ ⟧} {⟦ A ⟧})   = refl
  ~-ext {γ = γ} A pf (suc x)
    rewrite pf x
          | ∘/assoc (⟦var⟧ x) (π₁ {_} {⟦ A ⟧}) (γ ⋆⋆ id)
          | π₁/proj (γ ∘ π₁) (id {⟦ A ⟧} ∘ π₂)
          | ∘/assoc (⟦var⟧ x) γ (π₁ {_} {⟦ A ⟧})         = refl

  embed-pres : (ε : OPE Δ Γ) (a : Tm Γ A) (γ : ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧)
             → ε ~ γ
             → ℰ⟦ embed a ε ⟧ ≡ ℰ⟦ a ⟧ ∘ γ
  embed-pres ε tt γ pf
    rewrite !/uniq (! ∘ γ) = refl
  embed-pres ε < a , b > γ pf
    rewrite embed-pres ε a γ pf
          | embed-pres ε b γ pf
          | ⋆-∘-dist ℰ⟦ a ⟧ ℰ⟦ b ⟧ γ = refl
  embed-pres ε (fst a) γ pf
    rewrite embed-pres ε a γ pf | ∘/assoc π₁ ℰ⟦ a ⟧ γ = refl
  embed-pres ε (snd a) γ pf
    rewrite embed-pres ε a γ pf | ∘/assoc π₂ ℰ⟦ a ⟧ γ = refl
  embed-pres ε (ƛ_ {A = A} b) γ pf
    rewrite embed-pres (keep ε) b (γ ⋆⋆ id) (~-ext A pf)
          | curry/subst ℰ⟦ b ⟧ γ                         = refl
  embed-pres ε (f · a) γ pf
    rewrite embed-pres ε f γ pf
          | embed-pres ε a γ pf
          | ∘/assoc eval ⟨ ℰ⟦ f ⟧ , ℰ⟦ a ⟧ ⟩ γ
          | ⋆-∘-dist ℰ⟦ f ⟧ ℰ⟦ a ⟧ γ           = refl
  embed-pres ε (var x) γ pf = pf x

  _∼_ : Sb Δ Γ → ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧ → Set
  _∼_ {_} {Γ} σ γ =
    ∀ {A} (x : Γ ∋ A) → ℰ⟦ x ⟪ σ ⟫ ⟧ ≡ ⟦var⟧ x ∘ γ

  ∼-• : ∀ {σ : Sb Δ Γ} {γ : ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧}
      → σ ∼ γ → σ • a ∼ ⟨ γ , ℰ⟦ a ⟧ ⟩
  ∼-• {a = a} {γ = γ} pf zero
    rewrite π₂/proj γ (ℰ⟦ a ⟧) = refl
  ∼-• {a = a} {γ = γ} pf (suc x)
    rewrite pf x
          | ∘/assoc (⟦var⟧ x) π₁ ⟨ γ , ℰ⟦ a ⟧ ⟩
          | π₁/proj γ ℰ⟦ a ⟧                    = refl

  idₛ∼id : idₛ {Γ} ∼ id
  idₛ∼id (zero {Γ} {A})
    rewrite ∘/identityʳ (π₂ {⟦ Γ ⟧} {⟦ A ⟧}) = refl
  idₛ∼id (suc {Γ} {_} {B} x)
    rewrite commute-⟪ₛ∘ₑ⟫ idₛ (↑ {_} {B}) x
          | ⟪idₛ⟫-identity x
          | embed-var-idₑ-identity x
          | ∘/identityʳ (⟦var⟧ x ∘ π₁ {⟦ Γ ⟧} {⟦ B ⟧}) = refl

  ∼-ext : (σ : Sb Δ Γ)
        → {γ : ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧}
        → σ ∼ γ
        → ⌜keep⌝ {A = A} σ ∼ γ ⋆⋆ id {⟦ A ⟧}
  ∼-ext {Δ = Δ} σ {γ} pf {A} zero
    rewrite π₂/proj (γ ∘ π₁) (id {⟦ A ⟧} ∘ π₂)
          | ∘/identityˡ (π₂ {⟦ Δ ⟧} {⟦ A ⟧})   = refl
  ∼-ext σ {γ} pf {A} (suc {B = B} x)
    rewrite commute-⟪ₛ∘ₑ⟫ σ (↑ {_} {B}) x
          | embed-pres (↑ {_} {B}) (x ⟪ σ ⟫) π₁ (↑~π₁ {_} {B})
          | pf x
          | ∘/assoc (⟦var⟧ x) π₁ (γ ⋆⋆ id {⟦ B ⟧})
          | π₁/proj (γ ∘ π₁) (id {⟦ B ⟧} ∘ π₂)
          | ∘/assoc (⟦var⟧ x) γ (π₁ {_} {⟦ B ⟧})     = refl

  sub-pres : (σ : Sb Δ Γ) (a : Tm Γ A) (γ : ⟦ Δ ⟧ ⟶ ⟦ Γ ⟧)
           → σ ∼ γ
           → ℰ⟦ a [ σ ] ⟧ ≡ ℰ⟦ a ⟧ ∘ γ
  sub-pres σ tt γ pf rewrite !/uniq (! ∘ γ) = refl
  sub-pres σ < a , b > γ pf
    rewrite sub-pres σ a γ pf
          | sub-pres σ b γ pf
          | ⋆-∘-dist ℰ⟦ a ⟧ ℰ⟦ b ⟧ γ = refl
  sub-pres σ (fst p) γ pf
    rewrite sub-pres σ p γ pf
          | ∘/assoc π₁ ℰ⟦ p ⟧ γ = refl
  sub-pres σ (snd p) γ pf
    rewrite sub-pres σ p γ pf
          | ∘/assoc π₂ ℰ⟦ p ⟧ γ = refl
  sub-pres σ (ƛ_ {A = A} b) γ pf
    rewrite sub-pres (⌜keep⌝ σ) b (γ ⋆⋆ id) (∼-ext σ pf)
         | curry/subst ℰ⟦ b ⟧ γ                          = refl
  sub-pres σ (f · a) γ pf
    rewrite sub-pres σ f γ pf
          | sub-pres σ a γ pf
          | ∘/assoc eval ⟨ ℰ⟦ f ⟧ , ℰ⟦ a ⟧ ⟩ γ
          | ⋆-∘-dist ℰ⟦ f ⟧ ℰ⟦ a ⟧ γ           = refl
  sub-pres σ (var x) γ pf = pf x

  ⟦sub⟧/equiv : ∀ (b : Tm (Γ • A) B) (a : Tm Γ A)
              → ℰ⟦ b [ idₛ • a ] ⟧ ≡ ℰ⟦ b ⟧ ∘ ⟨ id , ℰ⟦ a ⟧ ⟩
  ⟦sub⟧/equiv b a = sub-pres (idₛ • a) b ⟨ id , ℰ⟦ a ⟧ ⟩ (∼-• idₛ∼id)

  ℰ-sound : ∀ {a a′ : Tm Γ A}
          → a ≡βη a′
          → ℰ⟦ a ⟧ ≡ ℰ⟦ a′ ⟧
  ℰ-sound (β {b = b} {a = a})
    rewrite ⟦sub⟧/equiv b a
          | ⋆-expand (curry ℰ⟦ b ⟧) ℰ⟦ a ⟧
          | Eq.sym (∘/assoc eval (curry ℰ⟦ b ⟧ ⋆⋆ id) ⟨ id , ℰ⟦ a ⟧ ⟩)
          | eval/curry ℰ⟦ b ⟧                                         = refl
  ℰ-sound {Γ} {A ⇒ B} (η {f = f})
    rewrite embed-pres (↑ {_} {A}) f π₁ (↑~π₁ {_} {A})
          | Eq.sym (∘/identityˡ (π₂ {⟦ Γ ⟧} {⟦ A ⟧}))
          | curry/uniq ℰ⟦ f ⟧                          = refl
  ℰ-sound {a = fst < a , b >} β-fst = π₁/proj _ _
  ℰ-sound {a = snd < a , b >} β-snd = π₂/proj _ _
  ℰ-sound η-pair = ⋆/uniq _
  ℰ-sound {a = a} tt-uniq = !/uniq _
  ℰ-sound (cong-ƛ eq)
    rewrite ℰ-sound eq = refl
  ℰ-sound (cong-app eq₁ eq₂)
    rewrite ℰ-sound eq₁ | ℰ-sound eq₂ = refl
  ℰ-sound (cong-fst eq)
    rewrite ℰ-sound eq = refl
  ℰ-sound (cong-snd eq)
    rewrite ℰ-sound eq = refl
  ℰ-sound (cong-pair eq₁ eq₂)
    rewrite ℰ-sound eq₁ | ℰ-sound eq₂ = refl
  ℰ-sound refl = refl
  ℰ-sound (sym eq) = Eq.sym (ℰ-sound eq)
  ℰ-sound (trans eq₁ eq₂) = Eq.trans (ℰ-sound eq₁) (ℰ-sound eq₂)

  module semantics-lemmas where
    ⟪⌜embed⌝⟫≡embed-var : ∀ (ε : OPE Δ Γ) (x : Γ ∋ A)
                        → ℰ⟦ x ⟪ ⌜ ε ⌝ ⟫ ⟧ ≡ ℰ⟦ var (embed-var x ε) ⟧
    ⟪⌜embed⌝⟫≡embed-var (drop {_}{_}{B} ε) x
      rewrite commute-⟪ₛ∘ₑ⟫ ⌜ ε ⌝ (↑ {_} {B}) x
            | embed-pres (↑ {_} {B}) (x ⟪ ⌜ ε ⌝ ⟫) π₁ (↑~π₁ {_} {B})
            | ⟪⌜embed⌝⟫≡embed-var ε x                      = refl
    ⟪⌜embed⌝⟫≡embed-var (keep ε) zero = refl
    ⟪⌜embed⌝⟫≡embed-var (keep ε) (suc {B = B} x)
      rewrite commute-⟪ₛ∘ₑ⟫ ⌜ ε ⌝ (↑ {_} {B}) x
            | embed-pres (↑ {_} {B}) (x ⟪ ⌜ ε ⌝ ⟫) π₁ (↑~π₁ {_} {B})
            | ⟪⌜embed⌝⟫≡embed-var ε x                      = refl

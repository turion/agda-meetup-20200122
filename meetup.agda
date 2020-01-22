data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data Vec (A : Set) : ℕ → Set where
  Nil : Vec A Z
  _::_ : {n : ℕ} → A → Vec A n → Vec A (S n)

replicate : {A : Set} (n : ℕ) → A → Vec A n
replicate n a = {!   !}

record ℕAndVec (A : Set) : Set where
  field
    length : ℕ
    vector : Vec A length

replicateℕAndVec : {A : Set} (n : ℕ) → A → ℕAndVec A
replicateℕAndVec n a = {!   !}

data List (A : Set) : Set where
  LNil : List A
  LCons : A → List A → List A

lengthList : {A : Set} → List A → ℕ
lengthList list = {!   !}

listToℕAndVec : {A : Set} → List A → ℕAndVec A
listToℕAndVec list = {!   !}

data _≤_ : ℕ → ℕ → Set where
  Z≤n : {n : ℕ} → Z ≤ n
  Sn₁≤Sn₂ : {n₁ n₂ : ℕ} → n₁ ≤ n₂ → S n₁ ≤ S n₂

-- data SortedList where
--     Empty : SortedList
--     Cons

record Container : Set₁ where
  field
    Shape : Set
    Position : Shape → Set

record [[_]]_ (c : Container) (A : Set) : Set where
  field
    shape : Container.Shape c
    positions : Container.Position c shape → A

open [[_]]_

data Read : Set where
  read : Read

readerContainer : Set → Container
readerContainer R = record { Shape = Read ; Position = λ _ → R }

Reader : Set → Set → Set
Reader R A = R → A

readerToContainer : {R A : Set} → Reader R A → [[ readerContainer R ]] A
readerToContainer reader = {!   !}

containerToReader : {R A : Set} → [[ readerContainer R ]] A → Reader R A
containerToReader container = {!   !}

forallC : {A : Set} {c : Container} → (A → Set) → [[ c ]] A → Set
forallC {_} {c} predicate container
    = (position : Container.Position c (shape container))
    → predicate (positions container position)

record existsC {A : Set} {c : Container} (predicate : A → Set) (container : [[ c ]] A) : Set where
  field
    position : Container.Position c (shape container)
    proof : predicate (positions container position)

readerSuc : [[ readerContainer ℕ ]] ℕ
readerSuc = {!   !}

atLeastOne : ℕ → Set
atLeastOne n = {!   !}

readerSucAtLeastOne : forallC atLeastOne readerSuc
readerSucAtLeastOne position = {!   !}

data MaybeFail (E : Set) : Set where
  Succeed : MaybeFail E
  FailBecause : E → MaybeFail E

data SuccessPosition : Set where
  success : SuccessPosition

data Failure : Set where

errPositions : {E : Set} → MaybeFail E → Set
errPositions maybeFail = {!   !}

errContainer : Set → Container
errContainer E = record { Shape = MaybeFail E ; Position = errPositions }

succeed : {A E : Set} → A → [[ errContainer E ]] A
succeed a = {!   !}

failBecause : {A E : Set} → E → [[ errContainer E ]] A
failBecause e = {!   !}

data SubtractionError : Set where
  unsignedOverflow : SubtractionError

checkedSub : ℕ → ℕ → [[ errContainer SubtractionError ]] ℕ
checkedSub n₁ n₂ = {!   !}

noErr : {A E : Set} → [[ errContainer E ]] A → Set
noErr {A} {E} container = {!   !}

canSubtractFromSuccessor : (n : ℕ) → noErr (checkedSub (S n) n)
canSubtractFromSuccessor _ = {!   !}

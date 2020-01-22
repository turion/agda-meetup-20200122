data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

data List (A : Set) : Set where
  LNil : List A
  LCons : A → List A → List A

myℕList : List ℕ
myℕList = LCons Z LNil

-- Vec : Set → ℕ → Set
data Vec (A : Set) : .ℕ → Set where
  Nil : Vec A Z
  _::_ : .{n : ℕ} → A → Vec A n → Vec A (S n)

myVec : Vec ℕ (S Z)
myVec = Z :: Nil

replicateList : {A : Set} → ℕ → A → List A
replicateList Z a = LNil
replicateList (S n) a = LCons a (replicateList n a)

vecOfLenN : Set → ℕ → Set
vecOfLenN A n = Vec A n

replicate : {A : Set} → A → (n : ℕ) → vecOfLenN A n
-- Pi type is:              ^^^^^^^^^^^^^^^^^
replicate a Z = Nil
replicate a (S n) = a :: replicate a n

replicateImplicit : {A : Set} {n : ℕ} → A → Vec A n
-- replicateImplicit {_} {n} a = replicate n a
replicateImplicit {_} {Z} a = Nil
replicateImplicit {A} {S n} a = a :: replicateImplicit {A} {n} a

record ℕAndVec (A : Set) : Set where
  field
    length : ℕ
    vector : Vec A length

replicateℕAndVec : {A : Set} (n : ℕ) → A → ℕAndVec A
replicateℕAndVec n a = {!   !}


lengthList : {A : Set} → List A → ℕ
lengthList list = {!   !}

listToℕAndVec : {A : Set} → List A → ℕAndVec A
listToℕAndVec list = {!   !}

data _≤_ : ℕ → ℕ → Set where
  Z≤n : {n : ℕ} → Z ≤ n
  Sn₁≤Sn₂ : {n₁ n₂ : ℕ} → n₁ ≤ n₂ → S n₁ ≤ S n₂


data SortedList : ℕ → Set where
  SNil : {n : ℕ} → SortedList n
  SCons : {n₂ : ℕ} → (n₁ : ℕ) → n₁ ≤ n₂ → SortedList n₂ → SortedList n₁

record Container : Set₁ where
  field
    Shape : Set
    Position : Shape → Set

-- Bool
data MaybeShape : Set where
  Just : MaybeShape
  Nothing : MaybeShape

-- Unit
data JustPosition : Set where
  just : JustPosition

-- Void
data NothingPosition : Set where

notsmaller : {n : ℕ} → S n ≤ n → NothingPosition
notsmaller = λ ()

maybePositions : MaybeShape → Set
maybePositions Just = JustPosition
maybePositions Nothing = NothingPosition

maybeContainer : Container
maybeContainer
  = record { Shape = MaybeShape ; Position = maybePositions }

record [[_]]_ (c : Container) (A : Set) : Set where
  field
    shape : Container.Shape c
    positions : Container.Position c shape → A
open [[_]]_

some : {A : Set} → A → [[ maybeContainer ]] A
some a = record { shape = Just ; positions = λ _ → a }

justAℕ : [[ maybeContainer ]] ℕ
justAℕ = some (S (S Z))

none : {A : Set} → [[ maybeContainer ]] A
none = record { shape = Nothing ; positions = λ () }

fmap : {c : Container} {A B : Set} → (A → B) → [[ c ]] A → [[ c ]] B
fmap f container = record
  { shape = shape container
  ; positions = λ p → f (positions container p)
  }

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

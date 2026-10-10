import Mathlib
import OAI.Computability.MinUncut.Search.FiniteEnumeration
import OAI.Computability.MinUncut.Estimates.WeightedTestLaw
import OAI.Computability.MinUncut.Encoding.QuestionEncoding

namespace OAI

section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
open MinUncutGames.Foundations.Hastad.SourceOccurrences

namespace SampleEnumeration

def fin (n : ℕ) : Enumeration (Fin n) := Enumeration.ofEncoding (Encoding.fin n)
def field : Enumeration F₂ := Enumeration.ofEncoding fieldEncoding

def point (m n : ℕ) : Enumeration (Point m n) := (fin m).function (fin n)
def row (m n : ℕ) : Enumeration (Row m n) :=
  (fin m).sigma (fun i => ((fin m).subtype (fun j => j≠i)).function (fin n))

local instance codeEq (m n : ℕ) : DecidableEq (Code m n) :=
  Subtype.instDecidableEq

def code (m n : ℕ) : Enumeration (Code m n) :=
  ((row m n).function field).image (faceSum m n).rangeRestrict (by
    intro z
    obtain ⟨f,hf⟩ := z.property
    exact ⟨f,Subtype.ext hf⟩)

local instance codeType (m n : ℕ) : Fintype (Code m n) :=
  Fintype.ofList (code m n).values (code m n).complete

abbrev Slots {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) :=
  Σ j, Fin (secondSlotCount (Q j))

def slots {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) : Enumeration (Slots Q) :=
  (fin t).sigma (fun j => fin (secondSlotCount (Q j)))

def formsPiEquiv (A : Type) [Fintype A] [DecidableEq A] :
    Forms (A → F₂) ≃ F₂ × (A → F₂) :=
  (AffineMap.toConstProdLinearMap F₂).toEquiv.trans
    (Equiv.prodCongr (Equiv.refl F₂) (LinearEquiv.piRing F₂ F₂ A F₂).toEquiv)

def formsCurryEquiv (A : Type) (B : A → Type) :
    Forms (∀a, B a → F₂) ≃ Forms ((Σa, B a) → F₂) :=
  AffineEquiv.arrowCongrEquiv
    (LinearEquiv.piCurry F₂ (fun (_ : A) (_ : B _) => F₂)).symm.toAffineEquiv
    (AffineEquiv.refl F₂ F₂)

def formsEquiv {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) :
    Forms (SecondAlphabet Q) ≃ F₂ × (Slots Q → F₂) :=
  (formsCurryEquiv (Fin t) (fun j => Fin (secondSlotCount (Q j)))).trans (formsPiEquiv (Slots Q))

local instance formEq {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) :
    DecidableEq (Forms (SecondAlphabet Q)) :=
  fun f g => decidable_of_iff (formsEquiv Q f=formsEquiv Q g) (formsEquiv Q).injective.eq_iff

def forms {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) : Enumeration (Forms (SecondAlphabet Q)) :=
  (field.pair ((slots Q).function field)).image (formsEquiv Q).symm (formsEquiv Q).symm.surjective

def arrays {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) :
    Enumeration (FaceArray (SecondAlphabet Q) m n) := (row m n).function (forms Q)

def coordinates (m n : ℕ) : Enumeration (TestCoordinates m n) :=
  Enumeration.ofEncoding ((point m n).encoding.sum ((point m n).encoding.sum (code m n).encoding))

def localSample {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) (g : GridData) :
    Enumeration (LocalSample (SecondAlphabet Q) m n g) := by
  letI : DecidableEq (Forms (SecondAlphabet Q)) := formEq Q
  letI : DecidableEq (FaceArray (SecondAlphabet Q) m n) := inferInstanceAs (DecidableEq (Row m n → Forms (SecondAlphabet Q)))
  exact (arrays Q m n).pair ((arrays Q m n).pair ((code m n).pair ((coordinates m n).function (fin g.L))))

def finsets (t : ℕ) : Enumeration (Finset (Fin t)) :=
  ((fin t).function (Enumeration.ofEncoding Encoding.bool)).image
    (fun f => Finset.univ.filter (fun j => f j=true)) (by
      intro S
      refine ⟨fun j => decide (j∈S),?_⟩
      ext j
      simp)

def fixedSets (t k : ℕ) : Enumeration (FixedSets (Fin t) k) :=
  (finsets t).subtype (fun H => H.card=k)

def outerSample (t s k : ℕ) : Enumeration (OuterSample (Fin t) (Fin s) k) :=
  (fixedSets t k).pair (((fin t).function (fin s)).pair ((fin t).function (fin 3)))

local instance localEq {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) (g : GridData) :
    DecidableEq (LocalSample (SecondAlphabet Q) m n g) := by
  letI : DecidableEq (Forms (SecondAlphabet Q)) := formEq Q
  letI : DecidableEq (FaceArray (SecondAlphabet Q) m n) :=
    inferInstanceAs (DecidableEq (Row m n → Forms (SecondAlphabet Q)))
  exact fun f h => decidable_of_iff
    (f.1=h.1 ∧ f.2.1=h.2.1 ∧ f.2.2.1=h.2.2.1 ∧ f.2.2.2=h.2.2.2)
    (by constructor <;> intro he <;> aesop)

def second {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) : Fin t → SecondQuestion (Fin N) :=
  fun j => if j∈o.1.val then Sum.inl ((eqs (o.2.1 j)).names (o.2.2 j)) else Sum.inr (eqs (o.2.1 j))

lemma second_eq {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) : second eqs o=sampleSecond eqs o := by
  funext j
  simp [second,sampleSecond,secondQuestion,sampleFirst,sampleHidden,hiddenSet,slotQuestion]

def semanticLocal {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) (m n : ℕ) (g : GridData) :
    Enumeration (LocalSample (SecondAlphabet (sampleSecond eqs o)) m n g) :=
  (second_eq eqs o) ▸ localSample (second eqs o) m n g

local instance semanticLocalEq {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) (m n : ℕ) (g : GridData) :
    DecidableEq (LocalSample (SecondAlphabet (sampleSecond eqs o)) m n g) :=
  (second_eq eqs o) ▸ localEq (second eqs o) m n g

def elementary {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) (k m n : ℕ) (g : GridData) :
    Enumeration (Elementary (I := Fin t) eqs k m n g) :=
  (outerSample t s k).sigma (fun o => semanticLocal eqs o m n g)

def tests : Enumeration Test :=
  Enumeration.ofList [.first,.second,.third,.fourth] (by intro j; cases j <;> simp)

def all {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) (k m n : ℕ) (g : GridData) :
    Enumeration (Test × Elementary (I := Fin t) eqs k m n g) :=
  tests.pair (elementary eqs k m n g)

end SampleEnumeration
end MinUncut.Outer

end

end OAI

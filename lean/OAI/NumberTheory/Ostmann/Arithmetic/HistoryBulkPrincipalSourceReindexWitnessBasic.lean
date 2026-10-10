import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilySymbolic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexWitness
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference HistoryBulkReferenceFrequencyFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkPrincipalSourceReindex HistoryCompensationRepresentativePatterns
open HistoryGiantOriginalMeanFactorization (Choices)
open HistoryGiantReferenceMean
open HistoryBulkFibreReference (originalMean)
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀j,(expand p b j).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)

abbrev leftDraws : Draws C (l:=l) := fun j=>blockSourceDraws C.sources
  (Template.initial (2*(bulkSize k L/2)) k) l p b hb (Sum.inl j)
abbrev rightDraws : Draws C (l:=l) := fun j=>blockSourceDraws C.sources
  (Template.initial (2*(bulkSize k L/2)) k) l p b hb (Sum.inr j)

def blockJacobian : ℂ := occurrenceJacobian C.sources
  (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l) (expand p b)

theorem blockJacobian_ne_zero : blockJacobian C p b ≠ 0 :=
  occurrenceJacobian_ne_zero C.sources _ (expand p b)

theorem choicePatternValue_of_valid
    (F : Choices (l:=l) C → Choices (l:=l) C → ℂ)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    choicePatternValue C F i.2.1 i.2.2 p b.val =
      F (leftChoices C (leftDraws C p b hb) i) (rightChoices C (rightDraws C p b hb) i) /
        blockJacobian C p b := by
  have he : extendSourceTest C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedChoiceTest C F i.2.1 i.2.2) (expand p b) =
      pairedChoiceTest C F i.2.1 i.2.2
        (blockSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l p b hb) :=
    dite_eq_left hb
  exact congrArg (fun z : ℂ=>z / blockJacobian C p b) he

variable (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (a : SelectedNonbulkSample C l)
  (J : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α → ℝ) (P Q : α → ℤ)

def fibreChoiceTest (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
    (c e : Choices (l:=l) C) : ℂ :=
  originalMean (selectedBulkPrior C l).mass w (fun u r=>
    weightedFibreTerm C outside σ a i.1.val i.1.val c e (J i) u (P r) (Q r))

def fibrePatternValue (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) : ℂ :=
  choicePatternValue C (fibreChoiceTest C outside σ a J w P Q i) i.2.1 i.2.2 p b.val

theorem fibrePatternValue_eq_wholeMean
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    fibrePatternValue C p b outside σ a J w P Q i =
      wholeMean C outside σ a (leftDraws C p b hb) (rightDraws C p b hb) J w P Q i /
        blockJacobian C p b :=
  choicePatternValue_of_valid C p b hb (fibreChoiceTest C outside σ a J w P Q i) i

theorem primeChoicePatternValue_eq_wholeMean
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    choicePatternValue C (fun c e=>weightedPrimeFibreMean C outside σ a i.1.val i.1.val c e (J i))
      i.2.1 i.2.2 p b.val =
      wholeMean C outside σ a (leftDraws C p b hb) (rightDraws C p b hb) J
        (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i / blockJacobian C p b := by
  simp_rw [weightedPrimeFibreMean_eq_weighted]
  exact fibrePatternValue_eq_wholeMean C p b hb outside σ a J
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i

theorem mixedChoicePatternValue_eq_wholeMean
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    choicePatternValue C (fun c e=>weightedMixedFibreMean C outside σ a i.1.val i.1.val c e (J i))
      i.2.1 i.2.2 p b.val =
      wholeMean C outside σ a (leftDraws C p b hb) (rightDraws C p b hb) J
        (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i /
          blockJacobian C p b := by
  simp_rw [weightedMixedFibreMean_eq_weighted]
  exact fibrePatternValue_eq_wholeMean C p b hb outside σ a J
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i

end Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexWitness

end

end OAI

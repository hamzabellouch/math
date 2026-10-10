import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorActualData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily
open HistorySelectedJointIntegralBounds HistoryBulkGiantIntegerReference
open HistoryGiantXiReplacementActual HistoryGiantReferenceSourceBounds HistorySignedXiTransport
open HistoryBulkIntegralReplacement HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistoryPairSmoothXi HistoryPairBulkCoordinates HistoryGiantReferenceMean HistoryBulkGiantCorrectedBounds

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem actualReference_left_supported (C : InitialSourceChoice d Bs BD Bz k L E) {l : ℕ} {outside : List ℕ}
    {σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))}
    {x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l} {i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l}
    {r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2}
    (a : ActualReferenceData C σ i r) :
    (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l
      (giantState (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) a.assignment i.1.val) a.plus a.minus)
      (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l i.2.1 x)).Supported (frequencyBound Bs BD Bz k L) outside := by
  exact a.left_eq ▸ r.left_supported

theorem actualReference_right_supported (C : InitialSourceChoice d Bs BD Bz k L E) {l : ℕ} {outside : List ℕ}
    {σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))}
    {x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l} {i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l}
    {r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2}
    (a : ActualReferenceData C σ i r) :
    (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l
      (giantState (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) (permutedAssignment C l σ a.assignment) i.1.val) a.plus a.minus)
      (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l i.2.2 y)).Supported (frequencyBound Bs BD Bz k L) outside := by
  exact a.right_eq ▸ r.right_supported

def actualNestedIntegral (C : InitialSourceChoice d Bs BD Bz k L E) {l : ℕ} {outside : List ℕ}
    {σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))}
    {x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l} {i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l}
    {r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2}
    (mixed : Bool) (s : ℕ) (a : ActualReferenceData C σ i r) : ℂ :=
  let c := assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l i.2.1 x
  let e := assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l i.2.2 y
  let h := decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l
    (giantState (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) a.assignment i.1.val) a.plus a.minus) c
  let g := decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l
    (giantState (sourceState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) (permutedAssignment C l σ a.assignment) i.1.val) a.plus a.minus) e
  let eB := integerOrderedEquiv C (frequencyBound Bs BD Bz k L) l outside σ a.assignment i.1.val i.1.val a.plus a.minus c e (actualReference_left_supported C a)
  if mixed then nestedMixedIntegral L C.giantCenter E
      (jointScalar C s h g (actualReference_left_supported C a) (actualReference_right_supported C a) (optionEquiv h g) eB)
  else nestedPrimeIntegral L C.giantCenter E
      (jointScalar C s h g (actualReference_left_supported C a) (actualReference_right_supported C a) (boolEquiv h g) eB)

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceCorrectedMeanOriginal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualDefs
import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization
open Construction Conclusion HistorySignedResidues HistorySignedXiTransport HistorySymbolicEncoding
open HistoryGiantReferenceMean HistoryGiantReferenceCounterpart HistoryGiantReferenceCorrectedMean
open HistoryGiantXiReplacementActual HistoryGiantPriorGrid
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

abbrev Seed := Template.initial (2*(bulkSize k L/2)) k
abbrev Current := Template.current (Seed (k:=k) (L:=L)) l
abbrev Choices := HistoryChoices C.sources (Seed (k:=k) (L:=L))
  (frequencyBound Bs BD Bz k L) l

def counterpart (y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (Q : ℤ) : ℂ :=
  (remainingCounterpartAt C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1)
    ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
    (C.compensationLogScale l) C.giantCenter (C.cells.center (bulkSize k L/2))
    (restoringAssignmentEquiv C.sources (l+1) _ y).1
    (restoringAssignmentEquiv C.sources (l+1) _ y).2 (Q:ℝ) : ℂ)

def originalPrimeMean (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  primeMean C.giant (sourceIntegrand d C.sources _ (frequencyBound Bs BD Bz k L) outside l
    (sourceState C.sources _ x s) (sourceState C.sources _ y t) c e
    (fun _ Q => counterpart C y Q) (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.bulkBin C.spectatorBin C.giantCenter)

def originalMixedMean (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  mixedMean C.giantCenter C.giant
    (sourceIntegrand d C.sources _ (frequencyBound Bs BD Bz k L) outside l
      (sourceState C.sources _ x s) (sourceState C.sources _ y t) c e
      (fun _ Q => counterpart C y Q) (bulkSize k L/2) (bulkSize k L/2)
      C.scale C.bulkBin C.spectatorBin C.giantCenter)

def history (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s P Q : ℤ) (c : Choices (l:=l) C) : History l :=
  decodeHistory C.sources _ (frequencyBound Bs BD Bz k L) l
    (giantState (sourceState C.sources _ x s) P Q) c

def compensationFactor
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  ((decodeHistory C.sources _ (frequencyBound Bs BD Bz k L) l
      (sourceState C.sources _ x s) c).compensationProduct:ℂ)*
    ((decodeHistory C.sources _ (frequencyBound Bs BD Bz k L) l
      (sourceState C.sources _ y t) e).compensationProduct:ℂ)

theorem compensationFactor_eq
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t P Q : ℤ) (c e : Choices (l:=l) C) :
    compensationFactor C x y s t c e =
      ((history C x s P Q c).compensationProduct:ℂ)*
        ((history C y t P Q e).compensationProduct:ℂ) := by
  unfold compensationFactor history
  rw [decoded_compensationProduct_eq C.sources _ _ l
      (giantState (sourceState C.sources _ x s) P Q) (sourceState C.sources _ x s) c,
    decoded_compensationProduct_eq C.sources _ _ l
      (giantState (sourceState C.sources _ y t) P Q) (sourceState C.sources _ y t) e]

variable (outside : List ℕ)
variable (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
variable (s t P Q : ℤ) (c e : Choices (l:=l) C)
variable (hs : (history C x s P Q c).Supported (frequencyBound Bs BD Bz k L) outside)
variable (gs : (history C y t P Q e).Supported (frequencyBound Bs BD Bz k L) outside)

theorem history_small_split :
    (history C y t P Q e).root.small = Template.reinsert (l+1) (Current (k:=k) (L:=L) (l:=l))
      (assignedSlots C.sources _ (restoringAssignmentEquiv C.sources (l+1) _ y).1)
      (assignedSlots C.sources _ (restoringAssignmentEquiv C.sources (l+1) _ y).2) := by
  simpa only [history,decodeHistory_root,giantState,sourceState] using
    assignedSlots_split_reinsert C.sources (l+1) _ y

theorem prime_reference_factor (n : ℕ) :
    primeMean C.giant (fun U W => counterpart C y W *
      referenceTerm d (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) hs gs n
        (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter U W) =
    (((history C x s P Q c).compensationProduct:ℂ)*
      ((history C y t P Q e).compensationProduct:ℂ))*
      guardedSourcePrimeMean (residueTransform d) (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) C.giantCenter ∅ C.giantPositive
        (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n)
        (pairModulus_dvd_comparisonModulus _ _ _ n)
        (primeScalar C (bulkSize k L/2) _ _ hs gs) := by
  exact prime_corrected_referenceMean_eq_guarded d _ outside _ _ hs gs n
    (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1)
    (restoringAssignmentEquiv C.sources (l+1) _ y).1
    (restoringAssignmentEquiv C.sources (l+1) _ y).2
    (history_small_split C y t P Q e) _ _ (C.cells.center (bulkSize k L/2)) ∅ C.giantPositive

theorem mixed_reference_factor (n : ℕ) :
    mixedMean C.giantCenter C.giant (fun U W => counterpart C y W *
      referenceTerm d (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) hs gs n
        (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter U W) =
    (((history C x s P Q c).compensationProduct:ℂ)*
      ((history C y t P Q e).compensationProduct:ℂ))*
      guardedSourceMixedMean (residueTransform d) (frequencyBound Bs BD Bz k L) outside
        (history C x s P Q c) (history C y t P Q e) C.giantCenter ∅ C.giantPositive
        (comparisonModulus (history C x s P Q c) (history C y t P Q e) outside n)
        (pairModulus_dvd_comparisonModulus _ _ _ n)
        (mixedScalar C (bulkSize k L/2) _ _ hs gs) := by
  exact mixed_corrected_referenceMean_eq_guarded d _ outside _ _ hs gs n
    (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
    C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1)
    (restoringAssignmentEquiv C.sources (l+1) _ y).1
    (restoringAssignmentEquiv C.sources (l+1) _ y).2
    (history_small_split C y t P Q e) _ _ (C.cells.center (bulkSize k L/2)) ∅ C.giantPositive

end Ostmann.Arithmetic.HistoryGiantOriginalMeanFactorization

end

end OAI

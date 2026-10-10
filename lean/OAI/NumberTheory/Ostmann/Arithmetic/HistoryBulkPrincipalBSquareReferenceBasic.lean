import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedPointwise
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedReferences

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryPairSourceCoordinates HistoryPairBulkCoordinates HistoryPairGiantCoordinates
open HistoryBulkReferenceTests HistoryPairBulkTransport HistoryPairKernelReplacement
open HistoryBulkFibreGiantApproximation HistoryPairVariableBSquareErrorSelected

theorem integerInsertOrderedGiants_representative {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (m depth : ℕ) (h k : History l) (hs : h.Supported V outside)
    (hh : Template.Matches (Template.current (Template.initial m depth) l) h.root.small)
    (z : Fin (2^l)×Fin m→ℤ) (u : Bool→ℤ) (r : Representative h k) :
    integerInsertOrderedGiants m depth h k hs hh z u (representativeMap h k r) =
      (prime h k r:ℤ) := by
  have hg : representativeMap h k r ∉ giantCoordinates h k := by
    obtain ⟨i,rfl⟩ := label_surjective h k r
    rcases i with i | i
    · exact left_small_not_mem h k (.inr i)
    · exact right_small_not_mem h k (.inr i)
  have hb : representativeMap h k r ∉ bulkCoordinates h k := by
    obtain ⟨i,rfl⟩ := label_surjective h k r
    rcases i with i | i
    · exact left_internal_not_mem h k i
    · exact right_internal_not_mem h k i
  simp only [integerInsertOrderedGiants,dite_eq_right hg,dite_eq_right hb,
    representativeMap_sample]

variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}

def leftDraw (r : Frame (l:=l) C outside) :
    DecodedDraw C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) outside l where
  root := assignedRoot C.sources _ r.s r.P.toNat r.Q.toNat r.leftSource
  choices := r.leftChoices
  sourceMatch := assignedRoot_matches C.sources _ r.s r.P.toNat r.Q.toNat r.leftSource
  supported := r.left_supported

def rightDraw (r : Frame (l:=l) C outside) :
    DecodedDraw C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
      (frequencyBound Bs BD Bz depth L) outside l where
  root := assignedRoot C.sources _ r.t r.P.toNat r.Q.toNat r.rightSource
  choices := r.rightChoices
  sourceMatch := assignedRoot_matches C.sources _ r.t r.P.toNat r.Q.toNat r.rightSource
  supported := r.right_supported

theorem fixedB_representative (r : Frame (l:=l) C outside)
    (x : Frame.Source (C:=C) (l:=l)) (q : Representative r.left r.right) :
    r.fixedB x (representativeMap r.left r.right q)=(prime r.left r.right q:ℤ) :=
  integerInsertOrderedGiants_representative _ _ _ _ _ _ _ _ q

def probabilityProduct (r : Frame (l:=l) C outside) (mixed : Bool)
    (x : Frame.Source (C:=C) (l:=l)) : ℝ :=
  ∏q : Representative r.left r.right,
    actualProbability mixed r.left r.right r.left_supported r.right_supported q
      (prime r.left r.right q) (r.fixedB x)

theorem decodedBProbabilityError_eq (r : Frame (l:=l) C outside) (mixed : Bool)
    (x : Frame.Source (C:=C) (l:=l)) :
    decodedBProbabilityError mixed (leftDraw r) (rightDraw r) (r.fixedB x) =
      (if mixed then r.mixedBMean x else r.unitBMean x) - (probabilityProduct r mixed x:ℂ) := by
  cases mixed <;> rfl

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI

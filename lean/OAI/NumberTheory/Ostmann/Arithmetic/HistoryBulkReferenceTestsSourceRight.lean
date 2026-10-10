import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesRight
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsSourceLeft

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTests
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryBulkSupportConversePlan
open HistoryBulkReferenceScalarCoordinates HistoryBulkSupportConverse

variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hπ : ∀i, sources ((Template.current (Template.initial m k₀) l).get (π i)).origin = sources ((Template.current (Template.initial m k₀) l).get i).origin)
  (c d : HistoryChoices sources (Template.initial m k₀) V l) {outside : List ℕ}
  (hs : (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c).Supported V outside)
  (hfixed : ∀i : Fin (Template.current (Template.initial m k₀) l).length, ((Template.current (Template.initial m k₀) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (Xp Xm : ℤ)
include hfixed

theorem integerInsertOrderedGiants_right_projection (q : Key (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d)) :
    integerInsertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedIntegerSourceValues sources m k₀ l x) (fun u => if u then Xm else Xp)
      (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) q) =
      newIntegerSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) Xp Xm
        ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀))).symm q) := by
  have he := insertOrderedGiants_right_projection sources m k₀ V l s t gp gm gp' gm'
    x₀ x π hπ c d hs hfixed Xp Xm q
  have hc := congrFun (integerInsertOrderedGiants_cast m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
    (orderedIntegerSourceValues sources m k₀ l x) (fun u => if u then Xm else Xp))
    (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) q)
  simp only [orderedIntegerSourceValues_cast, Int.cast_ite] at hc
  have hz := congrArg (fun r : ℚ => (r : ℝ))
    (congrFun (newIntegerSample_cast sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) Xp Xm)
      ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀))).symm q))
  simp only [Rat.cast_intCast] at hz
  exact_mod_cast hc.trans (he.trans hz.symm)

theorem source_right_lines_squares_of_B (ks : (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d).Supported V outside)
    (hB : orderedSourceIndicatorB sources m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) hs ks (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) x Xp Xm ≠ 0) :
    ∀ i : Internal (Template.initial m k₀) l,
      ((historyDraws sources (Template.initial m k₀) V l d i).val : ℤ) ∣
        referenceLine sources (Template.initial m k₀) V outside l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) ks Xp Xm i ∧
      ¬((historyDraws sources (Template.initial m k₀) V l d i).val : ℤ)^2 ∣
        referenceLine sources (Template.initial m k₀) V outside l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) ks Xp Xm i := by
  exact right_reference_lines_squares_of_B sources (Template.initial m k₀) V outside l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) ks
    (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) hs _ Xp Xm
    (integerInsertOrderedGiants_right_projection sources m k₀ V l s t gp gm gp' gm'
      x₀ x π hπ c d hs hfixed Xp Xm) hB

end Ostmann.Arithmetic.HistoryBulkReferenceTests

end

end OAI

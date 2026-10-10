import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesLeft
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportInsertion

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinates
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryBulkSupportConversePlan

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

theorem insertOrderedGiants_right_coordinate (i : Coordinate (Template.initial m k₀) l) :
    insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedSourceValues sources m k₀ l x) (fun u => if u then (Xm:ℝ) else (Xp:ℝ)) (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀))) i)) = (newSourceSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) Xp Xm i:ℝ) := by
  rcases i with u | i | i
  · change insertOrderedGiants _ _ _ _ _ _ _ _ (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (.inl u)) = _
    rw [insertOrderedGiants_right_giant]
    cases u <;> simp only [newSourceSample_plus,newSourceSample_minus,Rat.cast_intCast,
      Bool.false_eq_true,↓reduceIte]
  · change insertOrderedGiants _ _ _ _ _ _ _ _
      (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (coordinateEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (assignedLabels sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (.inr (.inl i)))) = _
    rw [assigned_right_root_key sources (Template.initial m k₀) V l s t gp gm x₀ π hπ c d i]
    have hl := insertOrderedGiants_left_coordinate sources m k₀ V l s gp gm gp' gm'
      x₀ x c (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) hs hfixed Xp Xm (.inr (.inl (π i)))
    simp only [newSourceSample_assigned_root,sourceAssignmentPermutation_val,
      decodedCoordinateEquiv,assignedHistory] at hl ⊢
    convert hl using 1
  · change insertOrderedGiants _ _ _ _ _ _ _ _
      (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (.inr (.inr (internalEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (assignedLabels sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) i)))) = _
    rw [insertOrderedGiants_right_small,insertOrdered_right_internal,newSourceSample_internal,
      Rat.cast_natCast]
    change (((internalSlot (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (internalEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) (assignedLabels sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) i)).value:ℤ):ℝ) = _
    rw [Int.cast_natCast]
    exact congrArg (fun n : ℕ => (n:ℝ))
      (decoded_internalSlot_eq_historyDraw sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) i)

theorem insertOrderedGiants_right_projection (q : Key (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d)) :
    insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedSourceValues sources m k₀ l x) (fun u => if u then (Xm:ℝ) else (Xp:ℝ)) (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀) d) q) = (newSourceSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x)) Xp Xm ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀))).symm q):ℝ) := by
  obtain ⟨i,rfl⟩ := (decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀)) d (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm (sourceAssignmentPermutation sources (Template.current (Template.initial m k₀) l) π hπ x₀))).surjective q
  rw [Equiv.symm_apply_apply]
  exact insertOrderedGiants_right_coordinate sources m k₀ V l s t gp gm gp' gm'
    x₀ x π hπ c d hs hfixed Xp Xm i

end Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinates

end

end OAI

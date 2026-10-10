import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinates
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryBulkSupportConversePlan

@[simp] theorem newSourceSample_assigned_root
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (l : ℕ)
    (s : ℤ) (gp gm : ℕ) (x : SourceAssignment sources (Template.current seed l))
    (c : HistoryChoices sources seed V l) (Xp Xm : ℤ)
    (i : Fin (Template.current seed l).length) :
    newSourceSample sources seed V l (assignedRoot sources _ s gp gm x) c
      (assignedRoot_matches sources _ s gp gm x) Xp Xm (.inr (.inl i)) = ((x i).val:ℚ) := by
  rw [newSourceSample_small]
  simp only [assignedRoot,assignedSlots,Template.sample,List.get_eq_getElem,List.getElem_ofFn]
  rfl

section Left
variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ→ℕ) (l : ℕ)
  (s : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ x : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (c : HistoryChoices sources (Template.initial m k₀) V l) (k : History l)
  {outside : List ℕ}
variable (hs : ((assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)).Supported V outside)
  (hfixed : ∀i : Fin ((Template.current (Template.initial m k₀) l)).length, ((Template.current (Template.initial m k₀) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (Xp Xm : ℤ)
include hfixed

theorem insertOrderedGiants_left_coordinate (i : Coordinate (Template.initial m k₀) l) :
    insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedSourceValues sources m k₀ l x) (fun t => if t then (Xm:ℝ) else (Xp:ℝ))
      (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k (decodedCoordinateEquiv sources (Template.initial m k₀) V l
        (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀) i)) =
      (newSourceSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) Xp Xm i:ℝ) := by
  rcases i with t | i | i
  · change insertOrderedGiants _ _ _ _ _ _ _ _ (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k (.inl t)) = _
    rw [insertOrderedGiants_left_giant]
    cases t <;> simp only [newSourceSample_plus,newSourceSample_minus,Rat.cast_intCast,
      Bool.false_eq_true,↓reduceIte]
  · change insertOrderedGiants _ _ _ _ _ _ _ _
      (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k (.inr (.inl (matchedRootPosition (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) i)))) = _
    rw [insertOrderedGiants_left_small,newSourceSample_assigned_root,Rat.cast_natCast]
    by_cases hi : ((Template.current (Template.initial m k₀) l).get i).role=.bulk
    · let u : BulkPosition (Template.current (Template.initial m k₀) l) := ⟨i,hi⟩
      have he : orderedKey m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) (currentBulkPositionEquiv m k₀ l u) =
          rootKey (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k (matchedRootPosition (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) i) := by
        simp only [orderedKey,Equiv.symm_apply_apply,u]
      change insertOrdered _ _ _ _ _ _ _ (rootKey (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k _) = _
      rw [←he,insertOrdered_left]
      exact congrArg (fun v : BulkPosition (Template.current (Template.initial m k₀) l) =>
        ((x v.val).val:ℝ)) ((currentBulkPositionEquiv m k₀ l).symm_apply_apply u)
    · rw [insertOrdered_left_nonbulk m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
        (orderedSourceValues sources m k₀ l x) _ (by rwa [matchedRootPosition_role])]
      change (((((assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)).root.small.get (matchedRootPosition (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) i)).value:ℤ):ℝ) = _
      rw [Int.cast_natCast,matchedRootPosition_value (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c)) x₀
        (by simp only [assignedHistory,decodeHistory_root,assignedRoot])]
      exact_mod_cast (hfixed i hi).symm
  · change insertOrderedGiants _ _ _ _ _ _ _ _
      (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k (.inr (.inr (internalEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c) i)))) = _
    rw [insertOrderedGiants_left_small,insertOrdered_left_internal,newSourceSample_internal,
      Rat.cast_natCast]
    change (((internalSlot (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (internalEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c) i)).value:ℤ):ℝ) = _
    rw [Int.cast_natCast]
    exact congrArg (fun n : ℕ => (n:ℝ))
      (decoded_internalSlot_eq_historyDraw sources (Template.initial m k₀) V l
        (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) c
        (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀) i)

theorem insertOrderedGiants_left_projection (q : Key (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c)) :
    insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedSourceValues sources m k₀ l x) (fun t => if t then (Xm:ℝ) else (Xp:ℝ))
      (leftMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) k q) =
      (newSourceSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp' gm' x) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp' gm' x) Xp Xm
        ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀)).symm q):ℝ) := by
  obtain ⟨i,rfl⟩ := (decodedCoordinateEquiv sources (Template.initial m k₀) V l
    (assignedRoot sources (Template.current (Template.initial m k₀) l) s gp gm x₀) c (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) s gp gm x₀)).surjective q
  rw [Equiv.symm_apply_apply]
  exact insertOrderedGiants_left_coordinate sources m k₀ V l s gp gm gp' gm' x₀ x c k hs hfixed Xp Xm i

end Left
end Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinates

end

end OAI

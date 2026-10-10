import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceScalarCoordinatesLeft

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport
open Construction Construction.CanonicalOccurrenceTransport Conclusion
open HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates HistorySymbolicEncoding
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryBulkSupportConversePlan
open HistoryBulkReferenceScalarCoordinates

theorem assigned_right_root_key (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (s t : ℤ) (gp gm : ℕ)
    (x₀ y₀ : SourceAssignment sources (Template.current seed l))
    (π : Equiv.Perm (Fin (Template.current seed l).length))
    (hold : ∀i,(y₀ i).val=(x₀ (π i)).val)
    (c e : HistoryChoices sources seed V l) (i : Fin (Template.current seed l).length) :
    rightMap (assignedHistory sources seed V l s gp gm x₀ c)
      (assignedHistory sources seed V l t gp gm y₀ e)
      (coordinateEquiv seed (assignedHistory sources seed V l t gp gm y₀ e)
        (assignedLabels sources seed V l t gp gm y₀ e) (.inr (.inl i))) =
    leftMap (assignedHistory sources seed V l s gp gm x₀ c)
      (assignedHistory sources seed V l t gp gm y₀ e)
      (coordinateEquiv seed (assignedHistory sources seed V l s gp gm x₀ c)
        (assignedLabels sources seed V l s gp gm x₀ c) (.inr (.inl (π i)))) := by
  apply Subtype.ext
  change Sum.inr (l+1, coordinateSample seed (assignedHistory sources seed V l t gp gm y₀ e)
    (assignedLabels sources seed V l t gp gm y₀ e) (.inr (.inl i))) =
    Sum.inr (l+1, coordinateSample seed (assignedHistory sources seed V l s gp gm x₀ c)
      (assignedLabels sources seed V l s gp gm x₀ c) (.inr (.inl (π i))))
  rw [assigned_root_sample,assigned_root_sample,hold i]

variable (sources : SourceFamily) (m k₀ : ℕ) (V : ℕ → ℕ) (l : ℕ)
  (s t : ℤ) (gp gm gp' gm' : ℕ)
  (x₀ y₀ x y : SourceAssignment sources (Template.current (Template.initial m k₀) l))
  (π : Equiv.Perm (Fin (Template.current (Template.initial m k₀) l).length))
  (hold : ∀i,(y₀ i).val=(x₀ (π i)).val)
  (hnew : ∀i,(y i).val=(x (π i)).val)
  (c e : HistoryChoices sources (Template.initial m k₀) V l) {outside : List ℕ}
  (hs : (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c).Supported V outside)
  (hfixedLeft : ∀i:Fin (Template.current (Template.initial m k₀) l).length,((Template.current (Template.initial m k₀) l).get i).role≠.bulk → (x i).val=(x₀ i).val)
  (Xp Xm : ℤ)
include hold hnew hfixedLeft

theorem insertOrderedGiants_right_coordinate (i : Coordinate (Template.initial m k₀) l) :
    insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedSourceValues sources m k₀ l x) (fun u => if u then (Xm:ℝ) else (Xp:ℝ)) (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm y₀) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm y₀)) i)) = (newSourceSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' y) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' y) Xp Xm i:ℝ) := by
  rcases i with u | i | i
  · change insertOrderedGiants _ _ _ _ _ _ _ _ (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (.inl u)) = _
    rw [insertOrderedGiants_right_giant]
    cases u <;> simp only [newSourceSample_plus,newSourceSample_minus,Rat.cast_intCast,
      Bool.false_eq_true,↓reduceIte]
  · change insertOrderedGiants _ _ _ _ _ _ _ _
      (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (coordinateEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (assignedLabels sources (Template.initial m k₀) V l t gp gm y₀ e) (.inr (.inl i)))) = _
    rw [assigned_right_root_key sources (Template.initial m k₀) V l s t gp gm x₀ y₀ π hold c e i]
    have hl := HistoryBulkReferenceScalarCoordinates.insertOrderedGiants_left_coordinate
      sources m k₀ V l s gp gm gp' gm' x₀ x c (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs hfixedLeft Xp Xm (.inr (.inl (π i)))
    simp only [newSourceSample_assigned_root,hnew,decodedCoordinateEquiv,assignedHistory] at hl ⊢
    convert hl using 1
  · change insertOrderedGiants _ _ _ _ _ _ _ _
      (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (.inr (.inr (internalEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (assignedLabels sources (Template.initial m k₀) V l t gp gm y₀ e) i)))) = _
    rw [insertOrderedGiants_right_small,insertOrdered_right_internal,newSourceSample_internal,Rat.cast_natCast]
    change (((internalSlot (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (internalEquiv (Template.initial m k₀) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) (assignedLabels sources (Template.initial m k₀) V l t gp gm y₀ e) i)).value:ℤ):ℝ) = _
    rw [Int.cast_natCast]
    exact congrArg (fun n : ℕ => (n:ℝ))
      (decoded_internalSlot_eq_historyDraw sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm y₀) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm y₀) i)

theorem insertOrderedGiants_right_projection (q : Key (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e)) :
    insertOrderedGiants m k₀ (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) hs (root_matches (assignedLabels sources (Template.initial m k₀) V l s gp gm x₀ c))
      (orderedSourceValues sources m k₀ l x) (fun u => if u then (Xm:ℝ) else (Xp:ℝ)) (rightMap (assignedHistory sources (Template.initial m k₀) V l s gp gm x₀ c) (assignedHistory sources (Template.initial m k₀) V l t gp gm y₀ e) q) = (newSourceSample sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp' gm' y) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp' gm' y) Xp Xm ((decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm y₀) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm y₀)).symm q):ℝ) := by
  obtain ⟨i,rfl⟩ := (decodedCoordinateEquiv sources (Template.initial m k₀) V l (assignedRoot sources (Template.current (Template.initial m k₀) l) t gp gm y₀) e (assignedRoot_matches sources (Template.current (Template.initial m k₀) l) t gp gm y₀)).surjective q
  rw [Equiv.symm_apply_apply]
  exact insertOrderedGiants_right_coordinate sources m k₀ V l s t gp gm gp' gm'
    x₀ y₀ x y π hold hnew c e hs hfixedLeft Xp Xm i

end Ostmann.Arithmetic.HistoryBulkIndependentReferenceTransport

end

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesPermutation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairBulkCoordinates
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairGiantCoordinates
open HistoryActiveCoordinates
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
variable (m k₀ : ℕ) (h k : History l) (hs : h.Supported V outside)
  (hh : Template.Matches (Template.current (Template.initial m k₀) l) h.root.small)
  (x : Fin (2^l) × Fin m → ℝ)

theorem insertOrdered_frozen (i : PairKey h k) (hi : i ∉ bulkCoordinates h k) :
    insertOrdered m k₀ h k hs hh x i = pairBackground h k i := by
  simp only [insertOrdered, HistoryActiveCoordinates.insert, dite_eq_right hi]

@[simp] theorem insertOrdered_left_giant (b : Bool) :
    insertOrdered m k₀ h k hs hh x (leftMap h k (.inl b)) = (integerSample h (.inl b) : ℝ) := by
  rw [insertOrdered_frozen _ _ _ _ _ _ _ _ (left_giant_not_mem h k b)]
  simp only [pairBackground, leftMap_sample]

@[simp] theorem insertOrdered_right_giant (b : Bool) :
    insertOrdered m k₀ h k hs hh x (rightMap h k (.inl b)) = (integerSample h (.inl b) : ℝ) := by
  rw [← shared_giant]
  exact insertOrdered_left_giant m k₀ h k hs hh x b

@[simp] theorem insertOrdered_left_internal (i : InternalKey h) :
    insertOrdered m k₀ h k hs hh x (leftMap h k (.inr (.inr i))) =
      (integerSample h (.inr (.inr i)) : ℝ) := by
  rw [insertOrdered_frozen _ _ _ _ _ _ _ _ (left_internal_not_mem h k i)]
  simp only [pairBackground, leftMap_sample]

@[simp] theorem insertOrdered_right_internal (i : InternalKey k) :
    insertOrdered m k₀ h k hs hh x (rightMap h k (.inr (.inr i))) =
      (integerSample k (.inr (.inr i)) : ℝ) := by
  rw [insertOrdered_frozen _ _ _ _ _ _ _ _ (right_internal_not_mem h k i)]
  rfl

theorem insertOrdered_left_nonbulk (i : Fin h.root.small.length)
    (hi : (h.root.small.get i).role ≠ .bulk) :
    insertOrdered m k₀ h k hs hh x (leftMap h k (.inr (.inl i))) =
      (integerSample h (.inr (.inl i)) : ℝ) := by
  change insertOrdered m k₀ h k hs hh x (rootKey h k i) = _
  rw [insertOrdered_frozen _ _ _ _ _ _ _ _ (left_nonbulk_not_mem h k hs i hi)]
  simp only [pairBackground, rootKey, leftMap_sample]

theorem insertOrdered_right_nonbulk (e : RootMatching h k) (i : Fin k.root.small.length)
    (hi : (k.root.small.get i).role ≠ .bulk) :
    insertOrdered m k₀ h k hs hh x (rightMap h k (.inr (.inl i))) =
      (integerSample k (.inr (.inl i)) : ℝ) := by
  rw [insertOrdered_frozen _ _ _ _ _ _ _ _ (right_nonbulk_not_mem h k hs e i hi)]
  rfl

end Ostmann.Arithmetic.HistoryPairBulkCoordinates

end

end OAI

import OAI.MeasureTheory.Falconer.Frostman.Content

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal NNReal

theorem content_le_diameter {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) (E : Set X) :
    hausdorffContent s E ≤ (Metric.ediam E)^s := by
  classical
  let U : ℕ → Set X := fun n => if n = 0 then E else ∅
  have hcover : E ⊆ ⋃ n, U n := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0,by simpa [U] using hx⟩
  calc
    hausdorffContent s E ≤ ∑' n, (Metric.ediam (U n))^s := content_le_cover s E U hcover
    _ = (Metric.ediam E)^s := by
      rw [tsum_eq_single 0]
      · simp [U]
      · intro n hn
        simp [U,hn,ENNReal.zero_rpow_of_pos hs]

theorem content_finite_of_bounded {X : Type*} [MetricSpace X]
    {s : ℝ} (hs : 0 < s) {E : Set X} (hE : Bornology.IsBounded E) :
    hausdorffContent s E < ∞ :=
  (content_le_diameter hs E).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hs.le hE.ediam_ne_top))

theorem exists_positive_cover_bound {X : Type*} [MetricSpace X]
    (E : Set X) (hE : IsCompact E) {s : ℝ≥0} (hs : 0 < s)
    (hd : (s : ℝ≥0∞) < dimH E) :
    ∃ c : ℝ, 0 < c ∧ ∀ U : ℕ → Set X, E ⊆ ⋃ n, U n →
      ENNReal.ofReal c ≤ ∑' n, (Metric.ediam (U n))^(s : ℝ) := by
  have hp := content_positive_of_lt_dimH E hs hd
  have hf := content_finite_of_bounded (by exact_mod_cast hs : 0 < (s : ℝ)) hE.isBounded
  refine ⟨(hausdorffContent (s : ℝ) E).toReal,
    ENNReal.toReal_pos (ne_of_gt hp) (ne_of_lt hf),?_⟩
  intro U hU
  rw [ENNReal.ofReal_toReal (ne_of_lt hf)]
  exact content_le_cover _ E U hU

end PlanarFalconer

end OAI

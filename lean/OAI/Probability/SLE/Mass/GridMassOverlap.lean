import OAI.Probability.SLE.Mass.MassGridOverlap

namespace OAI

/-! Summing physical grid-cell masses costs only the fixed overlap constant,
independently of the radius and of the containing compact set. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma grid_indicator_sum_le {r : ℝ} (hr : 0 < r) (x : ℂ) :
    (∑' i : ℤ×ℤ, (closedBall (coverGridCenter r i) (2*r)).indicator (fun _ => (1:ℝ≥0∞)) x) ≤ 81 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro I
  let f := fun (i : ℤ×ℤ) (z : ℂ) =>
    (closedBall (coverGridCenter r i) (2*r)).indicator (fun _ => (1:ℝ≥0∞)) z
  have hbound : ∀ i z, f i z ≤ 1 := by
    intro i z
    by_cases hz : z ∈ closedBall (coverGridCenter r i) (2*r) <;> simp [f,hz]
  have hs : ∀ i z, f i z ≠ 0 → dist z (coverGridCenter r i) ≤ 3*r := by
    intro i z hz
    by_cases hm : z ∈ closedBall (coverGridCenter r i) (2*r)
    · have hh : dist z (coverGridCenter r i) ≤ 2*r := hm
      linarith
    · exact (hz (by simp [f,hm])).elim
  have hh := massGrid_cutoff_product_sum_le hr I f hbound hs x x
  have hdist : dist x x ≤ 6*r := by simp; positivity
  rw [ite_eq_left hdist] at hh
  have he : (∑ i∈I, f i x*f i x) = ∑ i∈I, f i x := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx : x ∈ closedBall (coverGridCenter r i) (2*r) <;> simp [f,hx]
  rwa [he] at hh

lemma grid_mass_sum_le (μ : Measure ℂ) {r : ℝ} (hr : 0 < r) :
    (∑' i : ℤ×ℤ, μ (closedBall (coverGridCenter r i) (2*r))) ≤ 81*μ univ := by
  calc
    _ = ∫⁻ x, ∑' i : ℤ×ℤ,
        (closedBall (coverGridCenter r i) (2*r)).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_tsum (fun i => (measurable_const.indicator measurableSet_closedBall).aemeasurable)]
      apply tsum_congr
      intro i
      rw [lintegral_indicator measurableSet_closedBall]
      simp
    _ ≤ ∫⁻ _x, (81:ℝ≥0∞) ∂μ := lintegral_mono (grid_indicator_sum_le hr)
    _ = _ := by simp

end SLEExactGauge

end

end OAI

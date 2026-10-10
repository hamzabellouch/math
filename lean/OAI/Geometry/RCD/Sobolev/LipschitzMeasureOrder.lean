import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! # Measure order detected by bounded Lipschitz functions -/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace RegularPointCoordinates

theorem measure_le_of_bounded_lipschitz_integral
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.InnerRegular]
    (h : ∀ (f : X → ℝ) (L : ℝ≥0), LipschitzWith L f →
      (∀ x, 0 ≤ f x) → (∃ C : ℝ, ∀ x, f x ≤ C) →
      (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  have hc (F : Set X) (hF : IsClosed F) : μ F ≤ ν F := by
    let δ (j : ℕ) : ℝ := 1 / (j + 1)
    have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
    let f (j : ℕ) (x : X) : ℝ := thickenedIndicator (hδ j) F x
    have hf (j : ℕ) : LipschitzWith (δ j).toNNReal⁻¹ (f j) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact (lipschitzWith_thickenedIndicator (hδ j) F).dist_le_mul x y
    have hh (j : ℕ) : (∫ x, f j x ∂μ) ≤ ∫ x, f j x ∂ν := by
      apply h (f j) _ (hf j) (fun x => (thickenedIndicator (hδ j) F x).coe_nonneg)
      exact ⟨1, fun x => by exact_mod_cast thickenedIndicator_le_one (hδ j) F x⟩
    have hd : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hm := tendsto_integral_thickenedIndicator_of_isClosed μ hF hδ hd
    have hn := tendsto_integral_thickenedIndicator_of_isClosed ν hF hδ hd
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ F) (measure_ne_top ν F)).mp
      (le_of_tendsto_of_tendsto hm hn (Eventually.of_forall hh))
  apply Measure.le_iff.mpr
  intro A hA
  rw [hA.measure_eq_iSup_isCompact μ]
  exact iSup_le fun C => iSup_le fun hCA => iSup_le fun hC =>
    (hc C hC.isClosed).trans (measure_mono hCA)

theorem measure_eq_of_bounded_lipschitz_integral
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.InnerRegular] [ν.InnerRegular]
    (h : ∀ (f : X → ℝ) (L : ℝ≥0), LipschitzWith L f →
      (∀ x, 0 ≤ f x) → (∃ C : ℝ, ∀ x, f x ≤ C) →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  apply le_antisymm
  · exact measure_le_of_bounded_lipschitz_integral μ ν fun f L hf h0 hC => (h f L hf h0 hC).le
  · exact measure_le_of_bounded_lipschitz_integral ν μ fun f L hf h0 hC => (h f L hf h0 hC).ge

end RegularPointCoordinates

end OAI

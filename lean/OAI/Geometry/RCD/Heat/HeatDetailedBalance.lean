import OAI.Geometry.RCD.Heat.HeatJointDensity

namespace OAI

/-! # Detailed balance from the self-adjoint Cheeger semigroup -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem indicatorConstLp_abs_le_one {s : Set X} (hs : MeasurableSet s) (hfin : μ s ≠ ∞) :
    ∀ᵐ x ∂μ, |indicatorConstLp 2 hs hfin (1 : ℝ) x| ≤ (1 : ℝ≥0) := by
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℝ))] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

namespace NoncollapsedRCD

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- The constructed measure preserves the self-adjoint pairing on
bounded square-integrable data. -/
theorem heatRadonMeasure_pair (t : ℝ) (ht : 0 < t)
    (f g : Lp ℝ 2 (hausdorff n X)) (Cf Cg : ℝ≥0)
    (hf : ∀ᵐ y ∂hausdorff n X, |f y| ≤ Cf)
    (hg : ∀ᵐ y ∂hausdorff n X, |g y| ≤ Cg) :
    (∫ x, f x * (∫ y, g y ∂hX.heatRadonMeasure hn p t ht x) ∂hausdorff n X) =
      ∫ y, g y * (∫ x, f x ∂hX.heatRadonMeasure hn p t ht y) ∂hausdorff n X := by
  let μ := hausdorff n X
  simp_rw [hX.heatRadonMeasure_integral_bounded hn p t ht _ g Cg hg,
    hX.heatRadonMeasure_integral_bounded hn p t ht _ f Cf hf]
  calc
    _ = inner ℝ f (heatAt μ hX.quadratic t g) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hX.boundedHeat_represents hn p g ⟨Cg, hg⟩ t ht] with x hx
      simpa only [Real.inner_apply] using congrArg (fun a => f x * a) hx.symm
    _ = inner ℝ g (heatAt μ hX.quadratic t f) := by
      rw [← heatAt_inner μ hX.quadratic t f g, real_inner_comm]
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hX.boundedHeat_represents hn p f ⟨Cf, hf⟩ t ht] with y hy
      simpa only [Real.inner_apply] using congrArg (fun a => g y * a) hy

theorem heatRadonMeasure_integral_indicator (t : ℝ) (ht : 0 < t) (x : X)
    {s : Set X} (hs : MeasurableSet s) (hfin : hausdorff n X s ≠ ∞) :
    (∫ y, indicatorConstLp 2 hs hfin (1 : ℝ) y ∂hX.heatRadonMeasure hn p t ht x) =
      (hX.heatRadonMeasure hn p t ht x).real s := by
  rw [integral_congr_ae ((hX.heatRadonMeasure_absolutelyContinuous hn p t ht x).ae_le
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℝ))))]
  simp [integral_indicator hs]

/-- Transition mass between finite-volume sets is symmetric. -/
theorem heatRadonMeasure_set_balance (t : ℝ) (ht : 0 < t)
    {s u : Set X} (hs : MeasurableSet s) (hu : MeasurableSet u)
    (hfs : hausdorff n X s ≠ ∞) (hfu : hausdorff n X u ≠ ∞) :
    (∫ x in s, (hX.heatRadonMeasure hn p t ht x).real u ∂hausdorff n X) =
      ∫ y in u, (hX.heatRadonMeasure hn p t ht y).real s ∂hausdorff n X := by
  have H := hX.heatRadonMeasure_pair hn p t ht
    (indicatorConstLp 2 hs hfs (1 : ℝ)) (indicatorConstLp 2 hu hfu (1 : ℝ)) 1 1
    (indicatorConstLp_abs_le_one (hausdorff n X) hs hfs)
    (indicatorConstLp_abs_le_one (hausdorff n X) hu hfu)
  simp_rw [hX.heatRadonMeasure_integral_indicator hn p t ht] at H
  simpa only [integral_indicatorConstLp_mul] using H

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI

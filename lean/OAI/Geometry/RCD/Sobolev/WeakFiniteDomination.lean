import OAI.Geometry.RCD.Metric.FiniteDensityMeasure
import Mathlib.MeasureTheory.Integral.Regular
import OAI.Geometry.RCD.Metric.MeasuredBallLaw

namespace OAI

/-! # Domination passes to weak limits of finite energy measures -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_finite_weak_domination {n : ℕ}
    (νs μs : ℕ → FiniteMeasure (Euclidean n)) (ν μ : FiniteMeasure (Euclidean n))
    (hν : Tendsto νs atTop (𝓝 ν)) (hμ : Tendsto μs atTop (𝓝 μ))
    (c : ℕ → ℝ≥0) (c₀ : ℝ≥0) (hc : Tendsto c atTop (𝓝 c₀))
    (hb : ∀ k, (νs k : Measure (Euclidean n))≤(c k : ℝ≥0∞) • (μs k : Measure (Euclidean n))) :
    (ν : Measure (Euclidean n))≤(c₀ : ℝ≥0∞) • (μ : Measure (Euclidean n)) := by
  have htest (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) :
      (∫ z, φ z ∂(ν : Measure (Euclidean n)))≤(c₀:ℝ)*∫ z, φ z ∂(μ : Measure (Euclidean n)) := by
    have hleft := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν φ
    have hright := (NNReal.continuous_coe.tendsto c₀ |>.comp hc).mul
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ φ)
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [] with k
    change (∫ z, φ z ∂(νs k : Measure (Euclidean n)))≤
      (c k:ℝ)*(∫ z, φ z ∂(μs k : Measure (Euclidean n)))
    have hh := integral_mono_measure (hb k) (ae_of_all _ hφ)
      ((φ.integrable (μs k : Measure (Euclidean n))).smul_measure ENNReal.coe_ne_top)
    simpa only [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul] using hh
  let : ((c₀:ℝ≥0∞) • (μ : Measure (Euclidean n))).OuterRegular :=
    Measure.OuterRegular.smul _ ENNReal.coe_ne_top
  apply measure_le_of_open_sets
  intro U hU
  rw [hU.measure_eq_biSup_integral_continuous (ν : Measure (Euclidean n))]
  refine iSup_le fun f => iSup_le fun hf => iSup_le fun hf0 => iSup_le fun hfn => iSup_le fun hf1 => ?_
  let F : Euclidean n →ᵇ ℝ := ⟨⟨f,hf⟩,2,by
    intro x y
    calc dist (f x) (f y)≤dist (f x) 0+dist 0 (f y) := dist_triangle _ _ _
      _ ≤ 2 := by
        simp only [dist_zero_right,dist_zero_left,Real.norm_eq_abs,
          abs_of_nonneg (hfn x),abs_of_nonneg (hfn y)]
        have hx : f x≤(1:ℝ) := hf1 x
        have hy : f y≤(1:ℝ) := hf1 y
        linarith only [hx,hy]⟩
  have hh : (∫ z, f z ∂(ν : Measure (Euclidean n)))≤
      ∫ z, f z ∂((c₀:ℝ≥0∞) • (μ : Measure (Euclidean n))) := by
    rw [integral_smul_measure,ENNReal.coe_toReal,smul_eq_mul]
    exact htest F hfn
  exact (ENNReal.ofReal_le_ofReal hh).trans
    (integral_le_measure (fun x _ => hf1 x) (fun x hx => (hf0 hx).le))

end RegularPointCoordinates

end

end OAI

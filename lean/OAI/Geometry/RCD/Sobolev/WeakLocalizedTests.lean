import OAI.Geometry.RCD.Sobolev.BoundedTestCutoffError
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Weak probability limits tested on sets with continuous inner cutoffs -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

theorem weak_localized_test_tendsto {μ : ProbabilityMeasure X}
    {μs : ℕ → ProbabilityMeasure X} (hweak : Tendsto μs atTop (𝓝 μ))
    {s : Set X} (hs : MeasurableSet s)
    (hmass : Tendsto (fun k => (μs k : Measure X).real s) atTop (𝓝 ((μ : Measure X).real s)))
    (χ : ℕ → X →ᵇ ℝ) (hχ : ∀ m x, 0≤χ m x ∧ χ m x≤1)
    (hχ0 : ∀ m x, x∉s → χ m x=0)
    (hχlim : ∀ x, Tendsto (fun m => χ m x) atTop (𝓝 (s.indicator (fun _ => (1:ℝ)) x)))
    (φ : X →ᵇ ℝ) :
    Tendsto (fun k => ∫ x in s, φ x ∂(μs k : Measure X)) atTop
      (𝓝 (∫ x in s, φ x ∂(μ : Measure X))) := by
  have hcut := tendsto_integral_of_dominated_convergence (μ := (μ : Measure X))
    (fun _ => (1:ℝ)) (fun m => (χ m).continuous.aestronglyMeasurable)
    (integrable_const 1) (fun m => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hχ m x).1]
      exact (hχ m x).2) (Eventually.of_forall hχlim)
  simp only [integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one] at hcut
  have hdef : Tendsto (fun m => (μ : Measure X).real s-∫ x, χ m x ∂(μ : Measure X))
      atTop (𝓝 0) := by simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (μ : Measure X).real s)
          atTop (𝓝 ((μ : Measure X).real s))).sub hcut
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let B := ‖φ‖
  let δ := η/(4*(B+1))
  have hB : 0≤B := norm_nonneg φ
  have hδ : 0<δ := div_pos hη (by positivity)
  have heq : (B+1)*δ=η/4 := by
    dsimp only [δ]
    field_simp
  have hBδ : B*δ≤η/4 := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
  obtain ⟨m,hm⟩ := (hdef.eventually (Iio_mem_nhds hδ)).exists
  have hd := hmass.sub (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (χ m))
  have hp := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (χ m*φ)
  have hdev := hd.eventually (Iio_mem_nhds hm)
  have hpev := (Metric.tendsto_nhds.mp hp) (η/4) (by positivity)
  filter_upwards [hdev,hpev] with k hk hpk
  have he₁ := bounded_test_cutoff_error (μs k : Measure X) hs φ (χ m) (hχ m) (hχ0 m)
  have he₂ := bounded_test_cutoff_error (μ : Measure X) hs φ (χ m) (hχ m) (hχ0 m)
  have he₁' : |(∫ x in s, φ x ∂(μs k : Measure X))-
      (∫ x, χ m x*φ x ∂(μs k : Measure X))|≤η/4 :=
    he₁.trans ((mul_le_mul_of_nonneg_left hk.le hB).trans hBδ)
  have he₂' : |(∫ x in s, φ x ∂(μ : Measure X))-
      (∫ x, χ m x*φ x ∂(μ : Measure X))|≤η/4 :=
    he₂.trans ((mul_le_mul_of_nonneg_left hm.le hB).trans hBδ)
  change |(∫ x in s, φ x ∂(μs k : Measure X))-(∫ x in s, φ x ∂(μ : Measure X))|<η
  have htriangle := abs_sub_le (∫ x in s, φ x ∂(μs k : Measure X))
    (∫ x, χ m x*φ x ∂(μs k : Measure X)) (∫ x in s, φ x ∂(μ : Measure X))
  have htriangle' := abs_sub_le (∫ x, χ m x*φ x ∂(μs k : Measure X))
    (∫ x, χ m x*φ x ∂(μ : Measure X)) (∫ x in s, φ x ∂(μ : Measure X))
  rw [abs_sub_comm (∫ x, χ m x*φ x ∂(μ : Measure X))] at htriangle'
  have hpk' : |(∫ x, χ m x*φ x ∂(μs k : Measure X))-
      (∫ x, χ m x*φ x ∂(μ : Measure X))|<η/4 := hpk
  linarith

end RegularPointCoordinates

end

end OAI

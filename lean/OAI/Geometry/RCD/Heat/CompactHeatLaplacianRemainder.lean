import OAI.Geometry.RCD.Heat.CompactHeatScalingDensity
import OAI.Geometry.RCD.Heat.HeatSecondSourcePairing

namespace OAI

/-! # Uniform disappearance of the test-Laplacian remainder

The density is the original scaling interpolation at every interior time.
Its exact mass one makes the bound independent of that time and of the
normalizing endpoint factors.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}

namespace CompactHeatScalingData
variable (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def laplacianRemainder (f : Lp ℝ 2 (hausdorff n X)) (a : ℝ)
    (k : ℕ) (t : Ioo (0 : ℝ) 1) : ℝ :=
  (ε k/4)^2 * ∫ x, heatSecondGeneratorAt (hausdorff n X) hX.quadratic a f x *
    D.interpolationDensity k t x ∂hausdorff n X

theorem laplacianRemainder_bound (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (t : Ioo (0 : ℝ) 1) :
    |D.laplacianRemainder f a k t| ≤
      (ε k/4)^2 * ((2*(n:ℝ)*(|K|+1/(a/2)))^2*(A:ℝ)) := by
  let := D.interpolationDensity_probability k t
  have hb := hX.heat_second_source_pairing_bound hn p hK f A hf ha
    (D.interpolationDensity k t) (D.interpolationDensity_continuous k t).measurable
    (fun x => (D.interpolationDensity_pos k t x).le)
  rw [laplacianRemainder,abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

theorem laplacianRemainder_tendstoUniformly (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a : ℝ} (ha : 0 < a)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly (D.laplacianRemainder f a) (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  have hb : Tendsto (fun k => (ε k/4)^2 *
      ((2*(n:ℝ)*(|K|+1/(a/2)))^2*(A:ℝ))) atTop (𝓝 0) := by
    convert ((hε0.div_const 4).pow 2).mul_const
      ((2*(n:ℝ)*(|K|+1/(a/2)))^2*(A:ℝ)) using 1
    norm_num
  filter_upwards [hb.eventually (gt_mem_nhds hδ)] with k hk t
  simpa only [dist_zero_left,Real.norm_eq_abs] using
    (D.laplacianRemainder_bound hK f A hf ha k t).trans_lt hk

end CompactHeatScalingData
end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

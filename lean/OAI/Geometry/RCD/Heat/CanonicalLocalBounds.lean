import OAI.Geometry.RCD.Heat.HeatOverlapFinite
import OAI.Geometry.RCD.Metric.BoundedRegionVolume

namespace OAI

/-! # Uniform kernel bounds on bounded sets without Gaussian assumptions -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_bounded_on_ball (t : ℝ) (ht : 0 < t) (x₀ : X) (L : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall x₀ L, ∀ y ∈ closedBall x₀ L,
      |hX.canonicalHeatKernel hn p t x y| ≤ M := by
  obtain ⟨r,C,hr,hC,hbound⟩ := hX.heatRadonDensity_square_bound hn p (t/2) (half_pos ht)
  obtain ⟨m,hm,hvol⟩ := hX.ball_volume_lower_on_bounded_region hn x₀ L r hr
  let q := C/Real.sqrt m
  have hq : 0 ≤ q := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hb (x : X) (hx : x ∈ closedBall x₀ L) :
      (∫ z, (hX.heatRadonDensity hn p (t/2) (half_pos ht) x z)^2 ∂hausdorff n X) ≤ q^2 := by
    have hv := hvol x (mem_closedBall.mp hx)
    have hd : C/Real.sqrt ((hausdorff n X).real (ball x r)) ≤ q :=
      div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr hm) (Real.sqrt_le_sqrt hv)
    exact (hbound x).2.trans (pow_le_pow_left₀ (by positivity) hd 2)
  refine ⟨q^2,sq_nonneg q,?_⟩
  intro x hx y hy
  rw [hX.canonicalHeatKernel_eq_density_product hn p t ht x y]
  apply (sq_le_sq₀ (abs_nonneg _) (sq_nonneg q)).mp
  have hcs := integral_mul_sq_le_integral_sq (hausdorff n X)
    (hX.heatRadonDensity hn p (t/2) (half_pos ht) x)
    (hX.heatRadonDensity hn p (t/2) (half_pos ht) y)
    (hX.heatRadonDensity_memLp_two hn p (t/2) (half_pos ht) x)
    (hX.heatRadonDensity_memLp_two hn p (t/2) (half_pos ht) y)
  exact hcs.trans (by
    calc
      _ ≤ q^2*q^2 := mul_le_mul (hb x hx) (hb y hy)
        (integral_nonneg fun z => sq_nonneg _) (sq_nonneg q)
      _ = _ := by ring)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

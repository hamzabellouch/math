import OAI.Geometry.RCD.Heat.HeatDensityL2
import OAI.Geometry.RCD.Heat.CanonicalHeatKernel
import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # Finiteness of every heat overlap from actual L² smoothing -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonDensity_product_integrable (t : ℝ) (ht : 0 < t) (x y : X) :
    Integrable (fun z => hX.heatRadonDensity hn p t ht x z *
      hX.heatRadonDensity hn p t ht y z) (hausdorff n X) :=
  (hX.heatRadonDensity_memLp_two hn p t ht x).integrable_mul
    (hX.heatRadonDensity_memLp_two hn p t ht y)

/-- The extended overlap is finite at every pair, with no Gaussian premise. -/
theorem heatOverlapKernel_finite (t : ℝ) (ht : 0 < t) (x y : X) :
    hX.heatOverlapKernel hn p t ht x y ≠ ∞ := by
  rw [hX.heatOverlapKernel_eq_lintegral hn p]
  have he : (fun z => ENNReal.ofReal (hX.heatRadonDensity hn p t ht x z) *
      ENNReal.ofReal (hX.heatRadonDensity hn p t ht y z)) =
      (fun z => ENNReal.ofReal (hX.heatRadonDensity hn p t ht x z *
        hX.heatRadonDensity hn p t ht y z)) := by
    funext z
    rw [ENNReal.ofReal_mul (hX.heatRadonDensity_nonneg hn p t ht x z)]
  rw [he]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => mul_nonneg
    (hX.heatRadonDensity_nonneg hn p t ht x z) (hX.heatRadonDensity_nonneg hn p t ht y z))).mp
      (hX.heatRadonDensity_product_integrable hn p t ht x y).hasFiniteIntegral |>.ne

theorem canonicalHeatKernel_eq_density_product (t : ℝ) (ht : 0 < t) (x y : X) :
    hX.canonicalHeatKernel hn p t x y =
      ∫ z, hX.heatRadonDensity hn p (t/2) (half_pos ht) x z *
        hX.heatRadonDensity hn p (t/2) (half_pos ht) y z ∂hausdorff n X := by
  rw [canonicalHeatKernel,dite_eq_left ht,hX.heatOverlapKernel_eq_lintegral hn p]
  simp_rw [← ENNReal.ofReal_mul (hX.heatRadonDensity_nonneg hn p (t/2) (half_pos ht) x _)]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => mul_nonneg
    (hX.heatRadonDensity_nonneg hn p (t/2) (half_pos ht) x z)
    (hX.heatRadonDensity_nonneg hn p (t/2) (half_pos ht) y z))
      (hX.heatRadonDensity_product_integrable hn p (t/2) (half_pos ht) x y).aestronglyMeasurable).symm

theorem canonicalHeatKernel_memLp_two_unconditional (t : ℝ) (ht : 0 < t) (x : X) :
    MemLp (hX.canonicalHeatKernel hn p t x) 2 (hausdorff n X) :=
  (memLp_congr_ae ((hX.canonicalHeatKernel_ae hn p t ht x).trans
    (hX.heatJointDensity_ae hn p t ht x))).mpr (hX.heatRadonDensity_memLp_two hn p t ht x)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

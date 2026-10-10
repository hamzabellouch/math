import Mathlib
import OAI.Geometry.WeakHessian.Measure.RadialCutoff
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz
import OAI.Geometry.WeakHessian.LocalBounds.GammaNatMulLeft

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.integral_eq_zero (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {u A : X → ℝ}
    (hu : IsLaplacian m u A) (hA : Integrable A m)
    (hD : Integrable (weakGradient m u) m) : ∫ x, A x ∂m = 0 := by
  have hχ (n : ℕ) : Sobolev m (radialCutoff o n) :=
    sobolev_of_lipschitz_compactSupport hfinite (radialCutoff_lipschitz o n)
      (radialCutoff_compact o n)
  have hlim : Tendsto (fun n => ∫ x, A x*radialCutoff o n x ∂m) atTop
      (𝓝 (∫ x, A x ∂m)) := by
    have H := tendsto_integral_of_dominated_convergence (fun x => |A x|)
      (fun n => hA.aestronglyMeasurable.mul
        (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using hA.norm)
      (fun n => ae_of_all _ fun x => by
        change |A x*radialCutoff o n x| ≤ |A x|
        rw [abs_mul,abs_of_nonneg (radialCutoff_nonneg o n x)]
        exact mul_le_of_le_one_right (abs_nonneg _) (radialCutoff_le_one o n x))
      (ae_of_all _ fun x => tendsto_const_nhds.mul (radialCutoff_tendsto o x))
    simpa only [Pi.mul_apply,mul_one] using H
  have hb (n : ℕ) : ‖∫ x, A x*radialCutoff o n x ∂m‖ ≤
      (((n:ℝ)+1)⁻¹)*(∫ x, weakGradient m u x ∂m) := by
    have he := congrArg Neg.neg (hu.2.2 (radialCutoff o n) (hχ n))
    simp only [neg_neg] at he
    rw [← he,norm_neg]
    have HI := norm_integral_le_of_norm_le (f := gamma m u (radialCutoff o n)) (hD.const_mul (((n:ℝ)+1)⁻¹)) (by
      filter_upwards [abs_gamma_le hfinite hpar hu.1.2.1 (hχ n).2.1,
        weakGradient_le_lipschitz hfinite (radialCutoff_lipschitz o n),
        weakGradient_nonneg (m := m) u] with x hg hc hnon
      change |gamma m u (radialCutoff o n) x| ≤ (((n:ℝ)+1)⁻¹)*weakGradient m u x
      have hcr : weakGradient m (radialCutoff o n) x ≤ (((n:ℝ)+1)⁻¹) := by
        simpa only [NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hc
      exact hg.trans ((mul_le_mul_of_nonneg_left hcr hnon).trans_eq (mul_comm _ _)))
    simpa only [integral_const_mul] using HI
  have hz : Tendsto (fun n => ∫ x, A x*radialCutoff o n x ∂m) atTop (𝓝 0) := by
    apply squeeze_zero_norm hb
    simpa only [one_div,zero_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (∫ x, weakGradient m u x ∂m)
  exact tendsto_nhds_unique hlim hz
end WeakHessian

end
end InlinedFile0

end OAI

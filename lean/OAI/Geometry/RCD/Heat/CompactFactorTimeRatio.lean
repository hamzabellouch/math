import OAI.Geometry.RCD.Heat.CanonicalHeatTimeRatio
import OAI.Geometry.RCD.Heat.CompactHeatFactors

namespace OAI

/-! # A scale-independent comparison for compact endpoint heat factors

The endpoint weight cancels by comparing the two kernels before integration.
This is the ratio needed in the logarithmic gradient estimate.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_time_ratio :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (F : C(S, ℝ)), (∀ a, 0 ≤ F a) →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ 1/2 → ∀ (x : X) (R : ℝ),
          0 ≤ R → (∀ a : S, dist x a ≤ R) → ∀ w : X,
          hX.compactHeatFactor hn p ν F t ht w ≤ A*Real.exp (D*R^2/t)*
            hX.compactHeatFactor hn p ν F (2*t) (by positivity) x := by
  obtain ⟨A,D,hA,hD,hk⟩ := hX.canonicalHeatKernel_time_ratio hn p
  refine ⟨A,D,hA,hD,?_⟩
  intro S _ ν _ F hF t ht ht1 x R hR hdist w
  let Q := A*Real.exp (D*R^2/t)
  have hi := compact_kernel_factor_integrable ν (hX.compactHeatFactorKernel hn p S t ht) F w
  have hj := compact_kernel_factor_integrable ν (hX.compactHeatFactorKernel hn p S (2*t) (by positivity)) F x
  change (∫ a, hX.canonicalHeatKernel hn p t w a * F a ∂ν) ≤
    Q*(∫ a, hX.canonicalHeatKernel hn p (2*t) x a * F a ∂ν)
  rw [← integral_const_mul]
  apply integral_mono hi (hj.const_mul Q)
  intro a
  have hcoef : A*Real.exp (D*(dist x a)^2/t) ≤ Q := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ ht.le
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ dist_nonneg hR).mpr (hdist a)) hD.le
  have hp := (hk t ht ht1 x w a).trans
    (mul_le_mul_of_nonneg_right hcoef (hX.canonicalHeatKernel_pos hn p (2*t) (by positivity) x a).le)
  change hX.canonicalHeatKernel hn p t w a * F a ≤
    Q * (hX.canonicalHeatKernel hn p (2*t) x a * F a)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (hF a)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

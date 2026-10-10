import OAI.Geometry.RCD.Heat.CanonicalHeatBackwardRatio
import OAI.Geometry.RCD.Heat.CompactHeatFactors

namespace OAI

/-! # Backward logarithmic time control for compact endpoint factors -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_log_backward_time_ratio :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (F : C(S, ℝ)), (∀ a, 0<F a) → ∀ (s t : ℝ) (hs : 0<s) (hst : s≤t), t≤1 →
        ∀ (x : X) (R : ℝ), 0≤R → (∀ a : S, dist x a≤R) →
        Real.log (hX.compactHeatFactor hn p ν F t (hs.trans_le hst) x)-
          Real.log (hX.compactHeatFactor hn p ν F s hs x)≤C+D*R^2/s := by
  obtain ⟨A,D,hA,hD,hkernel⟩ := hX.canonicalHeatKernel_backward_time_ratio hn p
  refine ⟨|Real.log A|,D,abs_nonneg _,hD,?_⟩
  intro S _ ν _ F hF s t hs hst ht1 x R hR hdist
  have ht : 0<t := hs.trans_le hst
  let B := A*Real.exp (D*R^2/s)
  have hratio : hX.compactHeatFactor hn p ν F t ht x≤B*hX.compactHeatFactor hn p ν F s hs x := by
    have hi := compact_kernel_factor_integrable ν (hX.compactHeatFactorKernel hn p S t ht) F x
    have hj := compact_kernel_factor_integrable ν (hX.compactHeatFactorKernel hn p S s hs) F x
    change (∫ a, hX.canonicalHeatKernel hn p t x a*F a ∂ν)≤
      B*(∫ a, hX.canonicalHeatKernel hn p s x a*F a ∂ν)
    rw [←integral_const_mul]
    apply integral_mono hi (hj.const_mul B)
    intro a
    have he : A*Real.exp (D*(dist x a)^2/s)≤B := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hs.le
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ dist_nonneg hR).mpr (hdist a)) hD.le
    have hh := (hkernel s t hs hst ht1 x a).trans
      (mul_le_mul_of_nonneg_right he (hX.canonicalHeatKernel_pos hn p s hs x a).le)
    change hX.canonicalHeatKernel hn p t x a*F a≤
      B*(hX.canonicalHeatKernel hn p s x a*F a)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (hF a).le
  have hp := hX.compactHeatFactor_positive hn p ν F hF t ht x
  have hq := hX.compactHeatFactor_positive hn p ν F hF s hs x
  have hl := Real.log_le_log hp hratio
  dsimp only [B] at hl
  rw [Real.log_mul (mul_pos hA (Real.exp_pos _)).ne' hq.ne',
    Real.log_mul hA.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  linarith only [hl,le_abs_self (Real.log A)]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

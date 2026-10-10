import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatBE
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatGammaContinuity
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatCurvatureContinuity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile199
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_variable_dissipation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af AAf ξ Bξ BBξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    (hAf : (cheeger_closedQuadraticEnergy h).IsFormGenerator Af AAf)
    (hξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator ξ Bξ)
    (hBξ : (cheeger_closedQuadraticEnergy h).IsFormGenerator Bξ BBξ)
    {Cf CAf CAAf Cξ CBξ : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf) (hCAAf : 0 ≤ CAAf)
    (hCξ : 0 ≤ Cξ) (hCBξ : 0 ≤ CBξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Af x| ≤ CAf)
    (hAAfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|AAf x| ≤ CAAf)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hBξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|Bξ x| ≤ CBξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    2*(∫ s in 0..T,∫ x,(cheegerHeat h s ξ x*(K-a*G x))*
      gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m (fun x => a*F x)) ≤
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x))-
      (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T f) (cheegerHeat h T f) x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  let E := fun s => ∫ x,cheegerHeat h s ξ x*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  let Z := fun s => ∫ x,(cheegerHeat h s ξ x*(K-a*G x))*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  have hc : ContinuousOn E (Icc 0 T) :=
    hrcd.weighted_heat_gamma_continuousOn hN hfull hfin o hV hVB h hf hξ hCf hCAf hCξ hfb hAfb hξb T
  have hZ : ContinuousOn Z (Icc 0 T) := by
    apply hrcd.weighted_heat_curvature_continuousOn hN hfull hfin o hV hVB h ξ hf hCf hCAf hfb hAfb
      ((continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable) (B := |K|+|a| *CG) _ T
    exact ae_of_all _ fun x => (abs_sub _ _).trans (by dsimp only [Pi.mul_apply]; rw [abs_mul]; gcongr; exact hGb x)
  have hd : ∀ t ∈ Ioo 0 T,HasDerivWithinAt E (deriv E t) (Ioi t) t := by
    intro t ht
    exact (hrcd.weighted_heat_interpolation_hasDerivAt hN hfull hfin o hV hVB h hf hAf hξ hBξ
      hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb ht.1 ht.2).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hi : ∀ t ∈ Ioo 0 T,2*Z t ≤ deriv E t := fun t ht =>
    hHess.rcd_weighted_heat_interpolation_BE hN hrcd hfull hfin o hF hFb hGb hGc ha h
      hf hAf hξ hBξ hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb hξ0 ht.1 ht.2
  have H := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hT hc hd
    ((hZ.const_mul 2).integrableOn_Icc) hi
  rw [intervalIntegral.integral_const_mul] at H
  simpa only [E,Z,sub_zero,sub_self,cheegerHeat_zero,one_apply_eq_self,ν,V] using H
end WeakHessian

end
end InlinedFile199

end OAI

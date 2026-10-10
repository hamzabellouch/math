import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatBE
import OAI.Geometry.WeakHessian.Curvature.GammaCurvatureLowerBound
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatGammaContinuity
import OAI.Geometry.WeakHessian.LocalBounds.ExponentialODE

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile197
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_gradient_estimate {K N : ℝ}
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
    (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
      (cheegerHeat h T f) (cheegerHeat h T f) x ∂exponentialMeasure m (fun x => a*F x)) ≤
    Real.exp (-(2*(K-a*CG))*T)*
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let E := fun s => ∫ x,cheegerHeat h s ξ x*
    gamma ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x ∂ν
  have hc : ContinuousOn E (Icc 0 T) :=
    hrcd.weighted_heat_gamma_continuousOn hN hfull hfin o hV hVB h hf hξ hCf hCAf hCξ hfb hAfb hξb T
  have hd : ∀ t ∈ Ioo 0 T,DifferentiableAt ℝ E t := by
    intro t ht
    exact (hrcd.weighted_heat_interpolation_hasDerivAt hN hfull hfin o hV hVB h hf hAf hξ hBξ
      hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb ht.1 ht.2).differentiableAt
  have hi : ∀ t ∈ Ioo 0 T,2*(K-a*CG)*E t ≤ deriv E t := by
    intro t ht
    have hgen : IsLaplacian ν (cheegerHeat h (T-t) f) (cheegerHeat h (T-t) Af) :=
      (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (Q.formGenerator_heat ν hf (T-t))
    have hcurv := gamma_curvature_lower_bound (k := fun x => K-a*G x) hnfin hgen.1
      (Lp.aestronglyMeasurable (cheegerHeat h t ξ))
      (cheegerHeat_bounded h ht.1.le hCξ ξ hξb) (cheegerHeat_nonneg h ht.1.le ξ hξ0)
      ((continuous_const.sub (continuous_const.mul hGc)).aestronglyMeasurable)
      (Ck := |K|+|a| *CG) (k0 := K-a*CG) (ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · have H := hHess.rcd_weighted_heat_interpolation_BE hN hrcd hfull hfin o hF hFb hGb hGc ha h
        hf hAf hξ hBξ hCf hCAf hCAAf hCξ hCBξ hfb hAfb hAAfb hξb hBξb hξ0 ht.1 ht.2
      change (K-a*CG)*E t ≤ _ at hcurv
      change 2*_ ≤ deriv E t at H
      linarith only [hcurv,H]
    · exact (abs_sub _ _).trans (by rw [abs_mul]; gcongr; exact hGb x)
    · have hx := (le_abs_self (G x)).trans (hGb x)
      nlinarith
  have H := exponential_ode_comparison hT hc hd hi
  simpa only [E,sub_zero,sub_self,cheegerHeat_zero,one_apply_eq_self,ν,V] using H
end WeakHessian

end
end InlinedFile197

end OAI

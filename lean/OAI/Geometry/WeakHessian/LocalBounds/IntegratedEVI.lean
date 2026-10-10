import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatEVI

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile52
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

lemma integrated_exponential_evi_of_ae {E H : ℝ → ℝ} {K b : ℝ} (hb : 0 ≤ b)
    (hE : AbsolutelyContinuousOnInterval E 0 b) (hH : ContinuousOn H (Icc 0 b))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 b), deriv E t/2+K/2*E t ≤ H t) :
    (Real.exp (K*b)*E b-E 0)/2 ≤ ∫ t in 0..b,Real.exp (K*t)*H t := by
  have hG : AbsolutelyContinuousOnInterval (fun t : ℝ => Real.exp (K*t)) 0 b :=
    (by fun_prop : ContDiffOn ℝ 1 (fun t : ℝ => Real.exp (K*t)) (uIcc 0 b)).absolutelyContinuousOnInterval
  have hF := hG.fun_mul hE
  have hHi : IntervalIntegrable (fun t => Real.exp (K*t)*H t) volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hb] using (show ContinuousOn (fun t : ℝ => Real.exp (K*t)) (Icc 0 b) by fun_prop).fun_mul hH
  have ha : ∀ᵐ t ∂volume.restrict (Icc 0 b),
      deriv (fun s => Real.exp (K*s)*E s) t/2 ≤ Real.exp (K*t)*H t := by
    filter_upwards [hbound,ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hE.ae_differentiableAt]
      with t ht htb hdt
    have hd := (((hasDerivAt_id t).const_mul K).exp).mul (hdt (by simpa only [uIcc_of_le hb] using htb)).hasDerivAt
    have hd' : HasDerivAt (fun s => Real.exp (K*s)*E s)
        (Real.exp (K*t)*K*E t+Real.exp (K*t)*deriv E t) t := by
      convert! hd using 1
      simp
    rw [hd'.deriv]
    have H := mul_le_mul_of_nonneg_left ht (Real.exp_pos (K*t)).le
    nlinarith
  have H := intervalIntegral.integral_mono_ae_restrict hb (hF.intervalIntegrable_deriv.div_const 2) hHi ha
  rw [intervalIntegral.integral_div,hF.integral_deriv_eq_sub] at H
  simpa only [mul_zero,Real.exp_zero,one_mul] using H

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_integrated {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    (Real.exp (K*b)*quadraticWassersteinSq (μ b:Measure X) (ν:Measure X)-
      quadraticWassersteinSq (μ 0:Measure X) (ν:Measure X))/2 ≤
      ∫ t in 0..b,Real.exp (K*t)*(entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X)) := by
  exact integrated_exponential_evi_of_ae hb
    (hrcd.1.cheegerHeat_cost_ac hfin o h hu hun hi hV hU hA μ hμ ν
      (Measure.absolutelyContinuous_of_le_smul hdν) T hT hsν hW hb)
    (continuousOn_const.sub (hrcd.1.cheegerHeat_entropy_continuousOn hN hfull hfin o h hu hun hi hV hU hD hw μ hμ hb))
    (hrcd.cheegerHeat_comparison_ae hN hfull hfin o h hu hun hi hB huB hV hU hA hD hw μ hμ ν T hT
      hsν hCt hdν hW hW1 hb)
end WeakHessian

end
end InlinedFile52

end OAI

import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropyDensityBounds

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma integral_lipschitz_deviation {μ : Measure X} [IsProbabilityMeasure μ]
    {F : X → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (o : X)
    (hi : Integrable (fun x => dist x o) μ) :
    |(∫ x,F x ∂μ)-F o| ≤ (L:ℝ)*(∫ x,dist x o ∂μ) := by
  have hbound (x : X) : |F x-F o| ≤ (L:ℝ)*dist x o := by
    simpa only [Real.dist_eq] using hF.dist_le_mul x o
  have hd : Integrable (fun x => F x-F o) μ :=
    (hi.const_mul (L:ℝ)).mono' (hF.continuous.sub continuous_const).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hFi : Integrable F μ := by
    have H := hd.add (integrable_const (F o))
    change Integrable (fun x => F x-F o+F o) μ at H
    simpa only [sub_add_cancel] using H
  have H := abs_integral_le_integral_abs (f := fun x => F x-F o) (μ := μ)
  rw [integral_sub hFi (integrable_const (F o)),integral_const,probReal_univ,one_smul] at H
  exact H.trans (by
    rw [← integral_const_mul]
    exact integral_mono_ae hd.abs (hi.const_mul (L:ℝ)) (ae_of_all _ hbound))

lemma integral_dist_le_of_ae_ball {μ : Measure X} [IsProbabilityMeasure μ]
    (o : X) {r : ℝ} (hs : ∀ᵐ x ∂μ,dist x o ≤ r) :
    Integrable (fun x => dist x o) μ ∧ (∫ x,dist x o ∂μ) ≤ r := by
  have hi : Integrable (fun x => dist x o) μ := Integrable.of_bound (by fun_prop) r
    (hs.mono fun x hx => by simpa only [Real.norm_of_nonneg dist_nonneg] using hx)
  exact ⟨hi,by simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono_ae hi (integrable_const r) hs⟩

lemma backward_action_coarse {E D K a CG T : ℝ} (hE : 0 ≤ E) (hED : E ≤ D^2)
    (ha : 0 ≤ a) (hCG : 0 ≤ CG) (hT : 0 ≤ T) :
    (∫ s in (0:ℝ)..1,E/Real.exp (2*(K-a*CG)*T*(1-s))/2) ≤
      D^2*Real.exp (2*(|K| *T+CG*(a*T)))/2 := by
  have hc : Continuous (fun s : ℝ => E/Real.exp (2*(K-a*CG)*T*(1-s))/2) := (continuous_const.div (by fun_prop) (fun _ => Real.exp_ne_zero _)).div_const 2
  have H := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (hc.intervalIntegrable 0 1) (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => D^2*Real.exp (2*(|K| *T+CG*(a*T)))/2) volume 0 1) (fun s hs => by
      have h0 : 0 ≤ 1-s := by linarith [hs.2]
      have h1 : 1-s ≤ 1 := by linarith [hs.1]
      have hg : 0 ≤ a*CG := mul_nonneg ha hCG
      have H : -(2*(K-a*CG)*T*(1-s)) ≤ 2*(|K| *T+CG*(a*T)) := by
        have hK := neg_le_abs K
        have hA : -K+a*CG ≤ |K|+a*CG := by linarith
        have h1' := mul_le_mul_of_nonneg_right hA h0
        have h2' := mul_le_mul_of_nonneg_left h1 (add_nonneg (abs_nonneg K) hg)
        nlinarith
      rw [show E/Real.exp (2*(K-a*CG)*T*(1-s)) =
          E*Real.exp (-(2*(K-a*CG)*T*(1-s))) by rw [div_eq_mul_inv,Real.exp_neg]]
      exact div_le_div_of_nonneg_right (mul_le_mul hED (Real.exp_le_exp.mpr H)
        (Real.exp_pos _).le (hE.trans hED)) (by norm_num : (0:ℝ) ≤ 2))
  simpa using H

variable {m : Measure X} [SigmaFinite m]

lemma weighted_coupling_entropy_bound {F : X → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    {a T c : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (o x₁ : X) (μ ν : ProbabilityMeasure X)
    (hμE : FiniteEntropy m (μ:Measure X)) (hνE : FiniteEntropy m (ν:Measure X))
    (hνi : Integrable (fun x => dist x o) (ν:Measure X))
    (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
    {B : ℝ≥0} (hB : 0 < B) (hμB : (μ:Measure X) ≤ (B:ℝ≥0∞) • m)
    {r : ℝ} (hs : ∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r) {A : ℝ}
    {q : Measure (X×X)}
    (hcost : (QuadraticTransportCost q).toReal ≤
      2*(A+T*(entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
        entropyReal (exponentialMeasure m (fun x => a*F x)) (ν:Measure X)))) :
    (QuadraticTransportCost q).toReal ≤ 2*A+
      2*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1+
        c*(∫ x,dist x o ∂(ν:Measure X)))+
      2*(a*T)*(F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r)) := by
  have hVm : Measurable (fun x => a*F x) := (continuous_const.mul hF.continuous).measurable
  have hVb : ∀ x, |a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hVi : Integrable (fun x => a*F x) (ν:Measure X) := Integrable.of_bound hVm.aestronglyMeasurable (|a| *CF)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hVb x)
  have hupper := entropyReal_exponential_upper hμE hVm hVb hB hμB
  have hlower := entropyReal_lower_confinement (V := fun x => c*dist x o) hνE
    (by simpa only [abs_of_nonneg hc] using hνi.const_mul |c|) he
  have hchange := entropyReal_exponentialMeasure hνE hVm hVi
  rw [integral_const_mul] at hupper hlower hchange
  have hFν := (abs_le.mp (integral_lipschitz_deviation hF o hνi)).2
  obtain ⟨hμi,hμr⟩ := integral_dist_le_of_ae_ball x₁ hs
  have hFμ := (abs_le.mp (integral_lipschitz_deviation hF x₁ hμi)).1
  have hFμ' := mul_le_mul_of_nonneg_left hμr L.property
  have hdrop : entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
      entropyReal (exponentialMeasure m (fun x => a*F x)) (ν:Measure X) ≤
      |Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1+c*(∫ x,dist x o ∂(ν:Measure X))+
        a*(F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r)) := by
    have H := le_abs_self (Real.log (B:ℝ))
    have Hf : (∫ x,F x ∂(ν:Measure X))-(∫ x,F x ∂(μ:Measure X)) ≤
        F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r) := by
      change (∫ x,F x ∂(ν:Measure X))-F o ≤ (L:ℝ)*(∫ x,dist x o ∂(ν:Measure X)) at hFν
      change -((L:ℝ)*(∫ x,dist x x₁ ∂(μ:Measure X))) ≤ (∫ x,F x ∂(μ:Measure X))-F x₁ at hFμ
      change (L:ℝ)*(∫ x,dist x x₁ ∂(μ:Measure X)) ≤ (L:ℝ)*r at hFμ'
      nlinarith only [hFν,hFμ,hFμ']
    have Ha := mul_le_mul_of_nonneg_left Hf ha
    linarith
  have H := mul_le_mul_of_nonneg_left hdrop hT
  nlinarith [hcost]

end WeakHessian

end
end

end OAI

import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.TwoLegEstimate

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [SigmaFinite m]
lemma entropy_exponential_drop_bound {F : X → ℝ} {L : ℝ≥0}
    (hF : LipschitzWith L F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (o x₁ : X) (μ ν : ProbabilityMeasure X)
    (hμE : FiniteEntropy m (μ:Measure X)) (hνE : FiniteEntropy m (ν:Measure X))
    (hνi : Integrable (fun x => dist x o) (ν:Measure X))
    (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
    {B : ℝ≥0} (hB : 0 < B) (hμB : (μ:Measure X) ≤ (B:ℝ≥0∞) • m)
    {r : ℝ} (hs : ∀ᵐ x ∂(μ:Measure X),dist x x₁ ≤ r) :
    entropyReal (exponentialMeasure m (fun x => a*F x)) (μ:Measure X)-
      entropyReal (exponentialMeasure m (fun x => a*F x)) (ν:Measure X) ≤
      |Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1+
        c*(∫ x,dist x o ∂(ν:Measure X))+
        a*(F o-F x₁+(L:ℝ)*((∫ x,dist x o ∂(ν:Measure X))+r)) := by
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
  exact hdrop

end WeakHessian

end
end

end OAI

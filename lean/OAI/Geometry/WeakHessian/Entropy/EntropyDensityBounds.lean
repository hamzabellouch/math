import Mathlib
import OAI.Geometry.WeakHessian.Calculus.RnDerivSmul
import OAI.Geometry.WeakHessian.Entropy.MulLogFenchel

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m μ : Measure X}
variable [SigmaFinite m] [IsProbabilityMeasure μ]

lemma entropyReal_le_log_density_cap (hμ : FiniteEntropy m μ)
    {B : ℝ≥0} (hB : 0 < B) (hd : μ ≤ (B : ℝ≥0∞) • m) :
    entropyReal m μ ≤ Real.log B := by
  have hr := hμ.1.ae_le (rnDeriv_le_of_le_smul hd)
  have hp := Measure.rnDeriv_pos hμ.1
  have ht := hμ.1.ae_le (Measure.rnDeriv_lt_top μ m)
  have hlog : ∀ᵐ x ∂μ,llr μ m x ≤ Real.log B := by
    filter_upwards [hr,hp,ht] with x hx hp ht
    change Real.log (μ.rnDeriv m x).toReal ≤ Real.log B
    apply (Real.log_le_log_iff (ENNReal.toReal_pos hp.ne' ht.ne)
      (show 0 < (B : ℝ) from hB)).mpr
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.coe_toReal B)
  simpa only [entropyReal,integral_const,probReal_univ,one_smul] using
    integral_mono_ae hμ.2 (integrable_const (Real.log (B : ℝ))) hlog

lemma entropyReal_lower_confinement (hμ : FiniteEntropy m μ) {V : X → ℝ}
    (hV : Integrable V μ) (he : Integrable (fun x => Real.exp (-V x)) m) :
    1-(∫ x,V x ∂μ)-(∫ x,Real.exp (-V x) ∂m) ≤ entropyReal m μ := by
  have hρ := Measure.integrable_toReal_rnDeriv (μ := μ) (ν := m)
  have hp := (integrable_toReal_rnDeriv_mul_iff hμ.1).mpr hV
  have hl := (integrable_rnDeriv_mul_log_iff hμ.1).mpr hμ.2
  have H := integral_mono_ae ((hp.neg.sub he).add hρ) hl (ae_of_all _ fun x => by
    have H := mul_log_fenchel (r := (μ.rnDeriv m x).toReal) (a := -V x) ENNReal.toReal_nonneg
    simpa only [mul_neg,Pi.add_apply,Pi.sub_apply,Pi.neg_apply] using H)
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply] at H
  have hiA := integral_add (hp.neg.sub he) hρ
  have hiS := integral_sub hp.neg he
  simp only [Pi.sub_apply,Pi.neg_apply] at hiA hiS
  rw [hiA,hiS,integral_neg,
    integral_toReal_rnDeriv_mul hμ.1,Measure.integral_toReal_rnDeriv hμ.1,
    ← entropyReal_eq_integral_density hμ.1] at H
  simp only [probReal_univ] at H
  linarith

lemma entropyReal_exponential_upper (hμ : FiniteEntropy m μ)
    {V : X → ℝ} (hV : Measurable V) {C : ℝ} (hC : ∀ x,|V x| ≤ C)
    {B : ℝ≥0} (hB : 0 < B) (hd : μ ≤ (B : ℝ≥0∞) • m) :
    entropyReal (exponentialMeasure m V) μ ≤ Real.log B - ∫ x,V x ∂μ := by
  have hi : Integrable V μ := Integrable.of_bound hV.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  rw [entropyReal_exponentialMeasure hμ hV hi]
  exact sub_le_sub_right (entropyReal_le_log_density_cap hμ hB hd) _

end WeakHessian

end
end

end OAI

import Mathlib

namespace OAI

open MeasureTheory Set

open scoped ENNReal NNReal

namespace SmallTilts

variable {Ω : Type*} [MeasurableSpace Ω]

lemma cauchy (μ : Measure Ω) (f g : Ω → ENNReal) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x,f x*g x ∂μ)≤(∫⁻ x,(f x)^2 ∂μ)^(1/2:ℝ)*(∫⁻ x,(g x)^2 ∂μ)^(1/2:ℝ) := by
  simpa only [Pi.mul_apply,ENNReal.rpow_two] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.aemeasurable hg.aemeasurable

lemma square_root_product (a b : ENNReal) :
    (a^(1/2:ℝ)*b^(1/2:ℝ))^2=a*b := by
  rw [mul_pow,← ENNReal.rpow_natCast,← ENNReal.rpow_natCast,← ENNReal.rpow_mul,← ENNReal.rpow_mul]
  norm_num

lemma cauchy_squared (μ : Measure Ω) (f g : Ω → ENNReal) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x,f x*g x ∂μ)^2≤(∫⁻ x,(f x)^2 ∂μ)*(∫⁻ x,(g x)^2 ∂μ) := by
  exact (pow_le_pow_left' (cauchy μ f g hf hg) 2).trans_eq (square_root_product _ _)

lemma exp_square (t : ℝ) : (ENNReal.ofReal (Real.exp t))^2=ENNReal.ofReal (Real.exp (2*t)) := by
  rw [← ENNReal.ofReal_pow (Real.exp_nonneg _),← Real.exp_nat_mul]
  norm_num

lemma normalizer_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (M : ℝ≥0)
    (hM : (∫⁻ x,ENNReal.ofReal (Real.exp (2*|Y x|)) ∂μ)≤M) :
    let N := ∫⁻ x,ENNReal.ofReal (Real.exp (Y x)) ∂μ
    N≠0 ∧ N≠⊤ ∧ N⁻¹≤(M:ENNReal) := by
  let N := ∫⁻ x,ENNReal.ofReal (Real.exp (Y x)) ∂μ
  let N' := ∫⁻ x,ENNReal.ofReal (Real.exp (-Y x)) ∂μ
  have hN : N≤(M:ENNReal) := by
    apply le_trans (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))) hM
    nlinarith [le_abs_self (Y x),abs_nonneg (Y x)]
  have hN' : N'≤(M:ENNReal) := by
    apply le_trans (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))) hM
    nlinarith [neg_le_abs (Y x),abs_nonneg (Y x)]
  have hc := cauchy_squared μ (fun x => ENNReal.ofReal (Real.exp (Y x/2)))
    (fun x => ENNReal.ofReal (Real.exp (-Y x/2)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hY.div_const 2)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hY.neg.div_const 2)))
  have hp (x) : ENNReal.ofReal (Real.exp (Y x/2))*ENNReal.ofReal (Real.exp (-Y x/2))=1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    have hz : Y x/2 + -Y x/2=0 := by ring
    rw [hz,Real.exp_zero,ENNReal.ofReal_one]
  have hsq (x) : (ENNReal.ofReal (Real.exp (Y x/2)))^2=ENNReal.ofReal (Real.exp (Y x)) := by
    rw [exp_square]; congr 2; ring
  have hsq' (x) : (ENNReal.ofReal (Real.exp (-Y x/2)))^2=ENNReal.ofReal (Real.exp (-Y x)) := by
    rw [exp_square]; congr 2; ring
  simp only [hp,hsq,hsq',lintegral_const,measure_univ,mul_one,one_pow] at hc
  have hprod : 1≤N*(M:ENNReal) := hc.trans (by gcongr)
  have h0 : N≠0 := by intro h;rw [h,zero_mul] at hprod; exact one_ne_zero (le_antisymm hprod bot_le)
  have ht : N≠⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hN
  refine ⟨h0,ht,?_⟩
  exact (ENNReal.inv_le_iff_le_mul (fun _ => h0) (fun h => (ht h).elim)).mpr hprod

end SmallTilts

end OAI

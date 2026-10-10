import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarMoments

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real Set MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate

def gaussianWeight (x : ℝ) : ℝ := exp (-x^2/2)
def gaussianNormalizer : ℝ := (sqrt (2*Real.pi))⁻¹

lemma gaussian_weight_factor (x : ℝ) :
    gaussianWeight x = exp ((-(1/4:ℝ)*x^2))*exp ((-(1/4:ℝ)*x^2)) := by
  unfold gaussianWeight
  rw [←exp_add]
  congr 1
  ring

lemma polynomial_weight_bound (x : ℝ) :
    (1+x^2)*exp ((-(1/4:ℝ)*x^2)) ≤ 4 := by
  have h := add_one_le_exp ((1/4:ℝ)*x^2)
  have h' : 1+x^2 ≤ 4*exp ((1/4:ℝ)*x^2) := by linarith
  have hm := mul_le_mul_of_nonneg_right h' (exp_pos ((-(1/4:ℝ)*x^2))).le
  have hh : rexp ((1/4:ℝ)*x^2)*rexp (-(1/4:ℝ)*x^2) = 1 := by
    rw [←exp_add,show (1/4:ℝ)*x^2+(-(1/4:ℝ)*x^2)=0 by ring,exp_zero]
  simpa only [mul_assoc,hh,mul_one] using hm

lemma polynomial_tail_bound {x : ℝ} (hx : 10 ≤ |x|) :
    (1+x^2)*exp ((-(1/4:ℝ)*x^2)) ≤ 101*exp (-25) := by
  have h := add_one_le_exp ((x^2-100)/4)
  have hx2 : 100 ≤ x^2 := by nlinarith [sq_abs x]
  have h' : 1+x^2 ≤ 101*exp ((x^2-100)/4) := by nlinarith only [h,hx2]
  have hm := mul_le_mul_of_nonneg_right h' (exp_pos ((-(1/4:ℝ)*x^2))).le
  rw [mul_assoc,←exp_add,show (x^2-100)/4+(-(1/4:ℝ)*x^2) = -25 by ring] at hm
  exact hm

lemma gaussian_tail_constant : 12928*exp (-25:ℝ) ≤ 1/1000000 := by
  have he : (27/10:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) he 25
  have hh : 12928000000 ≤ exp (25:ℝ) := by
    rw [show exp (25:ℝ) = (exp (1:ℝ))^25 by simp]
    norm_num at hp ⊢
    linarith only [hp]
  rw [exp_neg]
  have he25 := exp_pos (25:ℝ)
  apply (mul_le_mul_iff_of_pos_right he25).mp
  field_simp
  linarith only [hh]

lemma integrable_weighted {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ x, |f x| ≤ 32*(1+x^2)) :
    Integrable (fun x => f x*gaussianWeight x) volume := by
  have hbase := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul (128:ℝ)
  apply hbase.mono' (hf.mul (by unfold gaussianWeight; fun_prop))
  apply ae_of_all
  intro x
  change |f x*gaussianWeight x| ≤ _
  rw [abs_mul,abs_of_pos (show 0 < gaussianWeight x from exp_pos _)]
  calc
    |f x| *gaussianWeight x ≤ (32*(1+x^2))*gaussianWeight x :=
      mul_le_mul_of_nonneg_right (hb x) (exp_pos _).le
    _ = 32*((1+x^2)*exp ((-(1/4:ℝ)*x^2)))*exp ((-(1/4:ℝ)*x^2)) := by
      rw [gaussian_weight_factor]
      ring
    _ ≤ 128*exp ((-(1/4:ℝ)*x^2)) := by
      have hp := mul_le_mul_of_nonneg_right (polynomial_weight_bound x) (exp_pos ((-(1/4:ℝ)*x^2))).le
      nlinarith only [hp]

lemma gaussian_truncation {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ x, |f x| ≤ 32*(1+x^2)) :
    |(∫ x, f x*gaussianWeight x)-(∫ x in (-10:ℝ)..10, f x*gaussianWeight x)| ≤ 1/1000000 := by
  have hi := integrable_weighted hf hb
  let s : Set ℝ := Icc (-10) 10
  have hs : MeasurableSet s := measurableSet_Icc
  have hi' := ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul
    (3232*exp (-25:ℝ))).integrableOn (s := sᶜ)
  have hm : ∀ᵐ x ∂volume.restrict sᶜ,
      |f x*gaussianWeight x| ≤ (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2)) := by
    rw [ae_restrict_iff' hs.compl]
    apply ae_of_all
    intro x hx
    have hxabs : 10 ≤ |x| := by
      by_contra h
      have ha := abs_lt.mp (lt_of_not_ge h)
      exact hx ⟨ha.1.le,ha.2.le⟩
    rw [abs_mul,abs_of_pos (show 0 < gaussianWeight x from exp_pos _)]
    calc
      |f x| *gaussianWeight x ≤ (32*(1+x^2))*gaussianWeight x :=
        mul_le_mul_of_nonneg_right (hb x) (exp_pos _).le
      _ = 32*((1+x^2)*exp ((-(1/4:ℝ)*x^2)))*exp ((-(1/4:ℝ)*x^2)) := by
        rw [gaussian_weight_factor]; ring
      _ ≤ (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2)) := by
        have hp := mul_le_mul_of_nonneg_right (polynomial_tail_bound hxabs) (exp_pos ((-(1/4:ℝ)*x^2))).le
        nlinarith only [hp]
  have hnorm := (norm_integral_le_integral_norm (f := fun x => f x*gaussianWeight x)
    (μ := volume.restrict sᶜ)).trans (integral_mono_ae hi.integrableOn.norm hi' (by
      filter_upwards [hm] with x hx
      simpa only [Real.norm_eq_abs] using hx))
  have hfull : (∫ x in sᶜ, (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2))) ≤
      ∫ x, (3232*exp (-25:ℝ))*exp ((-(1/4:ℝ)*x^2)) := by
    apply integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => by positivity))
    exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _
  have hsqrt : sqrt (Real.pi/(1/4:ℝ)) ≤ 4 := by
    apply (sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [pi_lt_four]⟩
  simp only [integral_const_mul,integral_gaussian] at hfull
  have hlast : (3232*exp (-25:ℝ))*sqrt (Real.pi/(1/4:ℝ)) ≤ 12928*exp (-25:ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 3232*exp (-25:ℝ))]
  rw [Real.norm_eq_abs,setIntegral_compl hs hi] at hnorm
  have he : (∫ x in s, f x*gaussianWeight x) = ∫ x in (-10:ℝ)..10, f x*gaussianWeight x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-10:ℝ) ≤ 10)]
    exact integral_Icc_eq_integral_Ioc
  rw [he] at hnorm
  rw [integral_const_mul] at hnorm
  exact hnorm.trans (hfull.trans (hlast.trans gaussian_tail_constant))

lemma normalizer_bounds : (39894227/100000000:ℝ) ≤ gaussianNormalizer ∧
    gaussianNormalizer ≤ 39894229/100000000 := by
  have hpi0 := pi_pos
  have hpiL := pi_gt_d20
  have hpiU := pi_lt_d20
  have hp : 0 < sqrt (2*Real.pi) := sqrt_pos.2 (by positivity)
  have hs : sqrt (2*Real.pi)^2 = 2*Real.pi := sq_sqrt (by positivity)
  unfold gaussianNormalizer
  constructor
  · rw [inv_eq_one_div,le_div_iff₀ hp]
    nlinarith only [hs,hpiL,hpiU,hp]
  · rw [inv_eq_one_div,div_le_iff₀ hp]
    nlinarith only [hs,hpiL,hpiU,hp]

lemma affine_gaussian_integral (β : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ h, f h ∂Scalar.fieldLaw β) =
      gaussianNormalizer*(∫ x, f (β^2+β*x)*gaussianWeight x) := by
  have hl : HasLaw (fun x : ℝ => β^2+β*x) (Scalar.fieldLaw β) (gaussianReal 0 1) := by
    have h := gaussianReal_const_add (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) β) (β^2)
    convert! h using 1
    simp [Scalar.fieldLaw,Scalar.variance]
    congr 1
    exact Real.toNNReal_of_nonneg (sq_nonneg β)
  rw [←hl.integral_comp hf.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp [gaussianNormalizer,gaussianWeight]
  ring

end SKRatio.Certificate

end

end OAI

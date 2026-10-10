import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarDensity

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

section Covariance
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

lemma covariance_nonpos_of_pairwise {f r : ℝ → ℝ}
    (hf : Integrable f μ) (hr : Integrable r μ)
    (hfr : Integrable (fun x => f x*r x) μ)
    (hsign : ∀ x y, (f x-f y)*(r x-r y) ≤ 0) :
    (∫ x, f x*r x ∂μ) ≤ (∫ x, f x ∂μ)*(∫ x, r x ∂μ) := by
  have hpoint (x : ℝ) :
      f x*r x-f x*(∫ y, r y ∂μ)-r x*(∫ y, f y ∂μ)+(∫ y, f y*r y ∂μ) ≤ 0 := by
    have hc1 : Integrable (fun y => f x*r x-f x*r y) μ :=
      (integrable_const _).sub (hr.const_mul _)
    have hc : Integrable (fun y => f x*r x-f x*r y-r x*f y) μ :=
      hc1.sub (hf.const_mul _)
    have he (y : ℝ) : (f x-f y)*(r x-r y) = f x*r x-f x*r y-r x*f y+f y*r y := by ring
    have hi := integral_nonpos (μ := μ) (hsign x)
    simp_rw [he] at hi
    rw [integral_add hc hfr,
      integral_sub hc1 (hf.const_mul _),
      integral_sub (integrable_const _) (hr.const_mul _),integral_const_mul,integral_const_mul,
      integral_const] at hi
    simpa only [integral_const_mul,probReal_univ,smul_eq_mul,one_mul] using hi
  have hh := integral_nonpos (μ := μ) hpoint
  have hc1 : Integrable (fun x => f x*r x-f x*(∫ y, r y ∂μ)) μ := hfr.sub (hf.mul_const _)
  have hc : Integrable (fun x => f x*r x-f x*(∫ y, r y ∂μ)-r x*(∫ y, f y ∂μ)) μ :=
    hc1.sub (hr.mul_const _)
  rw [integral_add hc (integrable_const _),
    integral_sub hc1 (hr.mul_const _),
    integral_sub hfr (hf.mul_const _),integral_mul_const,integral_mul_const,integral_const] at hh
  simp only [probReal_univ,smul_eq_mul,one_mul] at hh
  nlinarith only [hh]
end Covariance

def likelihood (β z h : ℝ) : ℝ :=
  (β/z)*exp ((β^2-z^2)/2+(1/(2*β^2)-1/(2*z^2))*h^2)

lemma continuous_likelihood (β z : ℝ) : Continuous (likelihood β z) := by
  unfold likelihood
  fun_prop

lemma likelihood_pos {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (h : ℝ) :
    0 < likelihood β z h := mul_pos (div_pos hβ hz) (exp_pos _)

lemma fieldLaw_withDensity_likelihood {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    (fieldLaw β).withDensity (fun h => ENNReal.ofReal (likelihood β z h)) = fieldLaw z := by
  rw [fieldLaw,fieldLaw,gaussianReal_of_var_ne_zero _ (variance_ne_zero hβ),
    gaussianReal_of_var_ne_zero _ (variance_ne_zero hz),
    ←withDensity_mul _ (measurable_gaussianPDF _ _) ((continuous_likelihood β z).measurable.ennreal_ofReal)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro h
  simp only [Pi.mul_apply,gaussianPDF,←ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  exact (mul_comm _ _).trans (field_pdf_ratio hz hβ h).symm

lemma integral_likelihood {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    ∫ h, likelihood β z h ∂fieldLaw β = 1 := by
  have hh := integral_const (μ := fieldLaw z) (1:ℝ)
  rw [←fieldLaw_withDensity_likelihood hβ hz,
    integral_withDensity_eq_integral_toReal_smul ((continuous_likelihood β z).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at hh
  simpa only [ENNReal.toReal_ofReal (likelihood_pos hβ hz _).le,smul_eq_mul,mul_one,
    fieldLaw_withDensity_likelihood hβ hz,probReal_univ,one_mul] using hh

lemma likelihood_integrable_iff {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (f : ℝ → ℝ) :
    Integrable f (fieldLaw z) ↔ Integrable (fun h => f h*likelihood β z h) (fieldLaw β) := by
  rw [←fieldLaw_withDensity_likelihood hβ hz,
    integrable_withDensity_iff ((continuous_likelihood β z).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos hβ hz _).le]

lemma integral_mul_likelihood {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) (f : ℝ → ℝ) :
    ∫ h, f h*likelihood β z h ∂fieldLaw β = ∫ h, f h ∂fieldLaw z := by
  rw [←fieldLaw_withDensity_likelihood hβ hz,
    integral_withDensity_eq_integral_toReal_smul ((continuous_likelihood β z).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (likelihood_pos hβ hz _).le,smul_eq_mul,mul_comm]

lemma likelihood_mono_sq {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) {x y : ℝ} (hxy : x^2 ≤ y^2) :
    likelihood β z x ≤ likelihood β z y := by
  have hz : 0 < z := hβ.trans_le hβz
  have hi : 1/(2*z^2) ≤ 1/(2*β^2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  unfold likelihood
  apply mul_le_mul_of_nonneg_left _ (div_pos hβ hz).le
  apply exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hi)]

lemma integral_temperature_antitone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z)
    {f : ℝ → ℝ} (hf : Integrable f (fieldLaw β)) (hf' : Integrable f (fieldLaw z))
    (hanti : ∀ x y : ℝ, x^2 ≤ y^2 → f y ≤ f x) :
    ∫ h, f h ∂fieldLaw z ≤ ∫ h, f h ∂fieldLaw β := by
  have hz : 0 < z := hβ.trans_le hβz
  have hr : Integrable (likelihood β z) (fieldLaw β) := by
    simpa only [one_mul] using (likelihood_integrable_iff hβ hz (fun _ => (1:ℝ))).mp (integrable_const _)
  have hcov := covariance_nonpos_of_pairwise hf hr ((likelihood_integrable_iff hβ hz f).mp hf')
    (fun x y => by
      rcases le_total (x^2) (y^2) with hh|hh
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hanti x y hh))
          (sub_nonpos.mpr (likelihood_mono_sq hβ hβz hh))
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hanti y x hh))
          (sub_nonneg.mpr (likelihood_mono_sq hβ hβz hh)))
  simpa only [integral_mul_likelihood hβ hz,integral_likelihood hβ hz,mul_one] using hcov

lemma m_mono : Monotone m := by
  apply monotone_of_deriv_nonneg
    (fun r => (Calculus.hasDerivAt_tanh r).differentiableAt)
  intro r
  rw [(Calculus.hasDerivAt_tanh r).deriv]
  exact (v_pos r).le

lemma m_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ m h := by
  have hh' := m_mono hh
  simpa only [m,tanh_zero] using hh'

lemma m_abs_sq (x : ℝ) : m |x|^2 = m x^2 := by
  rcases le_total 0 x with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    simp only [m,tanh_neg,neg_sq]

lemma m_sq_mono_sq {x y : ℝ} (hxy : x^2 ≤ y^2) : m x^2 ≤ m y^2 := by
  rw [←m_abs_sq x,←m_abs_sq y]
  exact (sq_le_sq₀ (m_nonneg (abs_nonneg _)) (m_nonneg (abs_nonneg _))).mpr
    (m_mono (sq_le_sq.mp hxy))

lemma a_temperature_antitone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) : a z ≤ a β := by
  apply integral_temperature_antitone hβ hβz
    (memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2))
  intro x y hxy
  exact sub_le_sub_left (m_sq_mono_sq hxy) 1

def signMeanG (h : ℝ) : ℝ := (1-m h^2)*(7/4+m h^2)/((7/4)^2-m h^2)

def gSignFactor (h : ℝ) : ℝ := v h/((7/4)^2-m h^2)

lemma gSignFactor_denom (h : ℝ) : (2:ℝ) < (7/4)^2-m h^2 := by
  have hh := tanh_sq_lt_one h
  change m h^2 < 1 at hh
  linarith

lemma continuous_gSignFactor : Continuous gSignFactor :=
  continuous_v.div (continuous_const.sub (continuous_m.pow 2))
    (fun h => ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 2) (gSignFactor_denom h)))

lemma gSignFactor_abs_le (h : ℝ) : |gSignFactor h| ≤ 1 := by
  have hd : 0 < (7/4)^2-m h^2 := lt_trans (by norm_num) (gSignFactor_denom h)
  rw [gSignFactor,abs_of_nonneg (div_nonneg (v_pos h).le hd.le)]
  apply (div_le_one hd).mpr
  linarith [v_le_one h,gSignFactor_denom h]

lemma memLp_gSignFactor {μ : Measure ℝ} [IsProbabilityMeasure μ] : MemLp gSignFactor 2 μ :=
  MemLp.of_bound continuous_gSignFactor.aestronglyMeasurable 1
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using gSignFactor_abs_le h))

lemma g_sign_expansion (h : ℝ) :
    g h = (7/4)*gSignFactor h+m h*gSignFactor h := by
  have hm := m_bounds h
  have hd := gSignFactor_denom h
  have h0 : (7/4:ℝ)-m h ≠ 0 := by linarith [hm.2]
  have h1 : (7/4:ℝ)^2-m h^2 ≠ 0 := by linarith
  calc
    g h = v h/(7/4-m h) := by unfold g w; congr 1; ring
    _ = ((7/4+m h)*v h)/((7/4)^2-m h^2) :=
      (div_eq_div_iff h0 h1).mpr (by ring)
    _ = _ := by unfold gSignFactor; ring

lemma signMeanG_expansion (h : ℝ) :
    signMeanG h = (7/4)*gSignFactor h+m h^2*gSignFactor h := by
  unfold signMeanG gSignFactor v
  ring

lemma memLp_signMeanG {μ : Measure ℝ} [IsProbabilityMeasure μ] : MemLp signMeanG 2 μ := by
  have hi : MemLp (fun h => m h^2*gSignFactor h) 2 μ := by
    apply memLp_gSignFactor.of_le_mul
      ((continuous_m.pow 2).mul continuous_gSignFactor).aestronglyMeasurable (c := (1:ℝ))
    apply ae_of_all
    intro h
    change |m h^2*gSignFactor h| ≤ 1*|gSignFactor h|
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (tanh_sq_lt_one h).le (abs_nonneg _)
  convert! (memLp_gSignFactor.const_mul (7/4:ℝ)).add hi using 1
  exact funext signMeanG_expansion

lemma G_eq_signMeanG (β : ℝ) : G β = ∫ h, signMeanG h ∂fieldLaw β := by
  have hkey := sign_identity β gSignFactor continuous_gSignFactor.measurable
    (fun h => by simp only [gSignFactor,v,m,tanh_neg,neg_sq]) gSignFactor_abs_le
  have hf : Integrable gSignFactor (fieldLaw β) := memLp_gSignFactor.integrable (by norm_num)
  have hmf : Integrable (fun h => m h*gSignFactor h) (fieldLaw β) :=
    (memLp_m (p := 2)).integrable_mul memLp_gSignFactor
  have hm2f : Integrable (fun h => m h^2*gSignFactor h) (fieldLaw β) := by
    have hi := memLp_signMeanG.integrable (μ := fieldLaw β) (by norm_num : (1:ENNReal) ≤ 2)
    convert! hi.sub (hf.const_mul (7/4:ℝ)) using 1
    ext h
    simp only [Pi.sub_apply,signMeanG_expansion]
    ring
  unfold G
  simp_rw [g_sign_expansion,signMeanG_expansion]
  rw [integral_add (hf.const_mul _) hmf,integral_add (hf.const_mul _) hm2f,hkey]

lemma signMeanG_antitone_sq {x y : ℝ} (hxy : x^2 ≤ y^2) : signMeanG y ≤ signMeanG x := by
  let u := m x^2
  let t := m y^2
  have hu : 0 ≤ u := sq_nonneg _
  have hut : u ≤ t := m_sq_mono_sq hxy
  have ht : t ≤ 1 := (tanh_sq_lt_one y).le
  have hdenu : 0 < (7/4)^2-u := by dsimp [u]; linarith [gSignFactor_denom x]
  have hdent : 0 < (7/4)^2-t := by dsimp [t]; linarith [gSignFactor_denom y]
  change (1-t)*(7/4+t)/((7/4)^2-t) ≤ (1-u)*(7/4+u)/((7/4)^2-u)
  apply (div_le_div_iff₀ hdent hdenu).mpr
  have hprod : 0 ≤ (t-u)*(35/64+(49/16)*(u+t)-u*t) := by
    apply mul_nonneg (sub_nonneg.mpr hut)
    have hh : u*t ≤ u := by nlinarith only [mul_nonneg hu (sub_nonneg.mpr ht)]
    nlinarith only [hh,hu,hut]
  nlinarith only [hprod]

lemma G_temperature_antitone {β z : ℝ} (hβ : 0 < β) (hβz : β ≤ z) : G z ≤ G β := by
  simp_rw [G_eq_signMeanG]
  exact integral_temperature_antitone hβ hβz
    (memLp_signMeanG.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (memLp_signMeanG.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (fun _ _ => signMeanG_antitone_sq)

end SKRatio.Scalar

end

end OAI

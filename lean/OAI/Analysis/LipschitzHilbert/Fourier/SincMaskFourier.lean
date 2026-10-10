import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskMotion
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The bandwidth of the actual sinc masks. Multiplication by an affine
sinc is an average of frequency translations. Repeated multiplication
therefore enlarges a spectral annulus by the sum of the individual
bandwidths, with the explicit Mathlib `2π` normalization. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace LipschitzHilbert

private theorem integrable_affine_modulation {f : ℝ → ℂ} (hf : Integrable f)
    (a b : ℝ) : Integrable (fun x : ℝ => Complex.exp (↑(a*x+b : ℝ)*Complex.I)*f x) := by
  apply hf.bdd_mul (c := 1)
  · exact (by fun_prop : Continuous (fun x : ℝ => Complex.exp (↑(a*x+b : ℝ)*Complex.I))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x : ℝ => le_of_eq (Complex.norm_exp_ofReal_mul_I (a*x+b)))

/-- Frequency translation, with an arbitrary affine constant phase. -/
theorem fourier_affine_modulation (f : ℝ → ℂ) (a b xi : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp (↑(a*x+b : ℝ)*Complex.I)*f x) xi =
      Complex.exp (b*Complex.I)*𝓕 f (xi-a/(2*Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x : ℝ => by
    simp only [smul_eq_mul]
    rw [← mul_assoc,← Complex.exp_add]
    conv_rhs => rw [← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
    ring)

private theorem fourier_const_mul (f : ℝ → ℂ) (z : ℂ) (xi : ℝ) :
    𝓕 (fun x : ℝ => z*f x) xi = z*𝓕 f xi := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x : ℝ => by
    simp only [smul_eq_mul]
    ring)

private theorem fourier_add_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (xi : ℝ) :
    𝓕 (fun x : ℝ => f x+g x) xi = 𝓕 f xi+𝓕 g xi := by
  have hff : Integrable (fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*xi : ℝ)*Complex.I)*f x) := by
    convert integrable_affine_modulation hf (-2*Real.pi*xi) 0 using 1
    funext x
    congr 2
    push_cast
    ring
  have hgg : Integrable (fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*xi : ℝ)*Complex.I)*g x) := by
    convert integrable_affine_modulation hg (-2*Real.pi*xi) 0 using 1
    funext x
    congr 2
    push_cast
    ring
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul,mul_add]
  exact integral_add hff hgg

private theorem affine_cos_identity (a b x : ℝ) :
    (Real.cos (a*x+b) : ℂ) =
      (Complex.exp (↑(a*x+b : ℝ)*Complex.I)+Complex.exp (↑((-a)*x+(-b) : ℝ)*Complex.I))/2 := by
  rw [Complex.ofReal_cos,Complex.cos]
  have hneg : (-a)*x+(-b) = -(a*x+b) := by ring
  rw [hneg,Complex.ofReal_neg]

theorem fourier_affine_cos_mul {f : ℝ → ℂ} (hf : Integrable f) (a b xi : ℝ) :
    𝓕 (fun x : ℝ => (Real.cos (a*x+b):ℂ)*f x) xi =
      (Complex.exp (b*Complex.I)*𝓕 f (xi-a/(2*Real.pi))+
       Complex.exp (-b*Complex.I)*𝓕 f (xi+a/(2*Real.pi)))/2 := by
  have heq : (fun x : ℝ => (Real.cos (a*x+b):ℂ)*f x) =
      fun x : ℝ => (Complex.exp (↑(a*x+b : ℝ)*Complex.I)*f x+
        Complex.exp (↑((-a)*x+(-b) : ℝ)*Complex.I)*f x)/2 := by
    funext x
    rw [affine_cos_identity]
    ring
  rw [heq]
  have hplus := integrable_affine_modulation hf a b
  have hminus := integrable_affine_modulation hf (-a) (-b)
  have hdiv : (fun x : ℝ => (Complex.exp (↑(a*x+b : ℝ)*Complex.I)*f x+
      Complex.exp (↑((-a)*x+(-b) : ℝ)*Complex.I)*f x)/2) =
      (fun x : ℝ => (2:ℂ)⁻¹*(Complex.exp (↑(a*x+b : ℝ)*Complex.I)*f x+
      Complex.exp (↑((-a)*x+(-b) : ℝ)*Complex.I)*f x)) := by
    funext x
    ring
  rw [hdiv,fourier_const_mul,fourier_add_integrable hplus hminus]
  rw [fourier_affine_modulation,fourier_affine_modulation]
  simp only [neg_div,sub_neg_eq_add,Complex.ofReal_neg]
  ring

/-- Multiplication by an affine sinc preserves integrability. -/
theorem integrable_affine_sinc_mul {f : ℝ → ℂ} (hf : Integrable f) (a b : ℝ) :
    Integrable (fun x : ℝ => (Real.sinc (a*x+b):ℂ)*f x) := by
  apply hf.bdd_mul (c := 1)
  · exact (by fun_prop : Continuous (fun x : ℝ => (Real.sinc (a*x+b):ℂ))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x : ℝ => by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sinc_le_one (a*x+b))

/-- The sinc multiplier is the actual cosine average, including at its
zeros and at the origin; Fubini uses only integrability of the packet. -/
theorem fourier_affine_sinc_mul {f : ℝ → ℂ} (hf : Integrable f) (a b xi : ℝ) :
    𝓕 (fun x : ℝ => (Real.sinc (a*x+b):ℂ)*f x) xi =
      ∫ t in Ioc (0:ℝ) 1, 𝓕 (fun x : ℝ => (Real.cos (t*(a*x+b)):ℂ)*f x) xi := by
  let e : ℝ → ℂ := fun x : ℝ => Complex.exp (↑(-2*Real.pi*x*xi : ℝ)*Complex.I)
  have hprod : Integrable (fun p : ℝ×ℝ =>
      e p.1*(Real.cos (p.2*(a*p.1+b)):ℂ)*f p.1)
      (volume.prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    apply (hf.norm.comp_fst (volume.restrict (Ioc (0:ℝ) 1))).mono'
    · exact (((by fun_prop : Continuous (fun p : ℝ×ℝ =>
          e p.1*(Real.cos (p.2*(a*p.1+b)):ℂ))).aestronglyMeasurable).mul
          hf.aestronglyMeasurable.comp_fst)
    · exact Filter.Eventually.of_forall (fun p => by
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        have he : ‖e p.1‖ = 1 := Complex.norm_exp_ofReal_mul_I _
        rw [he,one_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _))
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hid (x : ℝ) : (Real.sinc (a*x+b):ℂ) =
      ∫ t in Ioc (0:ℝ) 1, (Real.cos (t*(a*x+b)):ℂ) := by
    rw [sinc_eq_integral_cos,intervalIntegral.integral_of_le zero_le_one]
    exact integral_complex_ofReal.symm
  have hint (x : ℝ) : e x*((Real.sinc (a*x+b)):ℂ)*f x =
      ∫ t in Ioc (0:ℝ) 1, e x*(Real.cos (t*(a*x+b)):ℂ)*f x := by
    rw [hid,integral_mul_const,integral_const_mul]
  simp only [smul_eq_mul,← mul_assoc]
  change (∫ x, e x*((Real.sinc (a*x+b)):ℂ)*f x) = _
  simp_rw [hint]
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    funext x
    simp only [e,smul_eq_mul]
    ring)

/-- No Fourier mass is introduced except translations by at most
`|a|/(2π)`. The offset `b` has no effect on the bandwidth. -/
theorem fourier_affine_sinc_mul_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (a b xi : ℝ)
    (hzero : ∀ eta : ℝ, |eta-xi| ≤ |a|/(2*Real.pi) → 𝓕 f eta = 0) :
    𝓕 (fun x : ℝ => (Real.sinc (a*x+b):ℂ)*f x) xi = 0 := by
  rw [fourier_affine_sinc_mul hf]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [show (fun x : ℝ => (Real.cos (t*(a*x+b)):ℂ)*f x) =
      (fun x : ℝ => (Real.cos ((t*a)*x+t*b):ℂ)*f x) by
        funext x; congr 3; ring,
    fourier_affine_cos_mul hf]
  have hbound : |t*a/(2*Real.pi)| ≤ |a|/(2*Real.pi) := by
    rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [abs_of_pos ht.1]
    exact ht.2
  have hlo : 𝓕 f (xi-t*a/(2*Real.pi)) = 0 := hzero _ (by
    simpa only [sub_sub_cancel_left,abs_neg] using hbound)
  have hhi : 𝓕 f (xi+t*a/(2*Real.pi)) = 0 := hzero _ (by
    simpa only [add_sub_cancel_left] using hbound)
  rw [hlo,hhi]
  simp

end LipschitzHilbert

end

end OAI

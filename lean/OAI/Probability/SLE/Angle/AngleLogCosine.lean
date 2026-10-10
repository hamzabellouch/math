import OAI.Probability.SLE.Multipoint.MultipointLogAngular
import OAI.Probability.SLE.Angle.AnglePolynomialGenerator

namespace OAI

/-! Smooth cosine coordinates in the actual logarithmic Loewner state.
These formulas are used to apply the Brownian generator to eigenpolynomials. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def logInverseNorm (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-q.1.im)*powerLogDensity κ 0 1 q x

def logCosine (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  (q.1.re-Real.sqrt κ*x)*logInverseNorm κ q x

lemma logInverseNorm_eq (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    logInverseNorm κ q x=Real.exp (-Real.log (greenLogNormSq κ q x)/2) := by
  unfold logInverseNorm powerLogDensity
  rw [← Real.exp_add]
  congr 1
  ring

lemma logInverseNorm_pos (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0<logInverseNorm κ q x := by rw [logInverseNorm_eq]; positivity

lemma logInverseNorm_sq (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    logInverseNorm κ q x^2=(greenLogNormSq κ q x)⁻¹ := by
  rw [logInverseNorm_eq,pow_two,← Real.exp_add,
    show -Real.log (greenLogNormSq κ q x)/2 + -Real.log (greenLogNormSq κ q x)/2 =
      -Real.log (greenLogNormSq κ q x) by ring,Real.exp_neg,
    Real.exp_log (greenLogNormSq_pos κ q x)]

lemma logCosine_eq_angle (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    logCosine κ q x=Real.cos (Multipoint.logAngle κ q x) := by
  have hn := Multipoint.logPoint_norm_pos κ q x
  have he : logInverseNorm κ q x=‖Multipoint.logPoint κ q x‖⁻¹ := by
    rw [logInverseNorm_eq,← Multipoint.logPoint_norm_sq,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [show -(2*Real.log ‖Multipoint.logPoint κ q x‖)/2 =
      -Real.log ‖Multipoint.logPoint κ q x‖ by ring,Real.exp_neg,Real.exp_log hn]
  rw [logCosine,he,Multipoint.logAngle,
    Complex.cos_arg (norm_pos_iff.mp hn),Multipoint.logPoint_re,div_eq_mul_inv]

lemma logCosine_abs_le_one (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    |logCosine κ q x|≤1 := by
  rw [logCosine_eq_angle]
  exact Real.abs_cos_le_one _

lemma logInverseNorm_spatial (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (logInverseNorm κ q)
      (logInverseNorm κ q x*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x) x := by
  apply ((powerLogDensity_spatial_derivative κ 0 1 q x).const_mul (Real.exp (-q.1.im))).congr_deriv
  unfold logInverseNorm
  ring

lemma logCosine_spatial (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (logCosine κ q)
      (-Real.sqrt κ*Real.exp (2*q.1.im)*logInverseNorm κ q x/greenLogNormSq κ q x) x := by
  apply (((hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))).mul
    (logInverseNorm_spatial κ q x)).congr_deriv
  simp only [Pi.sub_apply,id_eq]
  have hn := (greenLogNormSq_pos κ q x).ne'
  field_simp
  unfold greenLogNormSq
  ring

lemma logInverseNorm_contDiff (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => logInverseNorm κ p.1 p.2) := by
  unfold logInverseNorm
  exact ((Complex.imCLM.contDiff.comp contDiff_fst.fst).neg.exp).mul
    (powerLogDensity_contDiff κ 0 1)

lemma logCosine_contDiff (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => logCosine κ p.1 p.2) := by
  unfold logCosine
  exact ((Complex.reCLM.contDiff.comp contDiff_fst.fst).sub
    (contDiff_const.mul contDiff_snd)).mul (logInverseNorm_contDiff κ)

end SLEExactGauge

end

end OAI

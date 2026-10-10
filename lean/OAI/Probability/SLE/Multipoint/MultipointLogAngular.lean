import OAI.Probability.SLE.Multipoint.MultipointLogFactor
import OAI.Probability.SLE.Multipoint.MultipointAngular

namespace OAI

/-! Identification of the smooth logarithmic monomials with the angular
factors, in actual capacity-two coordinates. -/

noncomputable section
open Set

namespace SLEExactGauge.Multipoint

def logPoint (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℂ :=
  ((q.1.re-Real.sqrt κ*x : ℝ) : ℂ) + (Real.exp q.1.im : ℂ)*Complex.I

def logAngle (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ := (logPoint κ q x).arg

def logVelocity (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  Real.exp q.1.im / greenLogNormSq κ q x

lemma logPoint_re (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    (logPoint κ q x).re = q.1.re-Real.sqrt κ*x := by simp [logPoint]

lemma logPoint_im (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    (logPoint κ q x).im = Real.exp q.1.im := by
  simp only [logPoint, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add, add_zero]

lemma logPoint_norm_sq (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    ‖logPoint κ q x‖^2 = greenLogNormSq κ q x := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, logPoint_re, logPoint_im]
  have he : Real.exp q.1.im * Real.exp q.1.im = Real.exp (2*q.1.im) := by
    rw [← Real.exp_add]; congr 1; ring
  simpa only [greenLogNormSq, pow_two] using congrArg
    (fun y => (q.1.re-Real.sqrt κ*x)*(q.1.re-Real.sqrt κ*x)+y) he

lemma logPoint_norm_pos (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < ‖logPoint κ q x‖ := by
  apply norm_pos_iff.mpr
  intro h
  have him := congrArg Complex.im h
  rw [logPoint_im, Complex.zero_im] at him
  exact (Real.exp_pos q.1.im).ne' him

lemma logAngle_sin_pos (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < Real.sin (logAngle κ q x) := by
  rw [logAngle, Complex.sin_arg, logPoint_im]
  exact div_pos (Real.exp_pos _) (logPoint_norm_pos κ q x)

lemma logAngle_sin_sq (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    Real.sin (logAngle κ q x)^2 = Real.exp (2*q.1.im)/greenLogNormSq κ q x := by
  rw [logAngle, Complex.sin_arg, logPoint_im, div_pow, logPoint_norm_sq]
  have he : Real.exp q.1.im^2 = Real.exp (2*q.1.im) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  rw [he]

lemma logAngle_log_sin (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    Real.log (Real.sin (logAngle κ q x)) =
      q.1.im - Real.log (greenLogNormSq κ q x)/2 := by
  have hn := logPoint_norm_pos κ q x
  have hN : Real.log (greenLogNormSq κ q x) = 2*Real.log ‖logPoint κ q x‖ := by
    rw [← logPoint_norm_sq, Real.log_pow]
    norm_num
  rw [logAngle, Complex.sin_arg, logPoint_im, Real.log_div (Real.exp_ne_zero _) hn.ne',
    Real.log_exp, hN]
  ring

lemma logFactor_eq_angular (κ c r : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    logFactor κ c r q x = Real.exp ((c*κ/4)*(q.2-q.1.im))*
      sinePower r (logAngle κ q x) := by
  rw [sinePower, Real.rpow_def_of_pos (logAngle_sin_pos κ q x), ← Real.exp_add,
    logAngle_log_sin]
  unfold logFactor
  congr 1
  ring

lemma logVelocity_pos (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < logVelocity κ q x := div_pos (Real.exp_pos _) (greenLogNormSq_pos κ q x)

lemma logFactor_spatial_eq_angular (κ c r : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    deriv (logFactor κ c r q) x =
      Real.sqrt κ*logVelocity κ q x*Real.exp ((c*κ/4)*(q.2-q.1.im))*
        sinePowerFirst r (logAngle κ q x) := by
  rw [(logFactor_spatial_derivative κ c r q x).deriv, logFactor_eq_angular]
  unfold sinePowerFirst sinePower
  rw [Real.rpow_sub (logAngle_sin_pos κ q x), Real.rpow_one]
  have hn := logPoint_norm_pos κ q x
  have hz : logPoint κ q x ≠ 0 := norm_pos_iff.mp hn
  rw [logAngle, Complex.cos_arg hz, Complex.sin_arg, logPoint_re, logPoint_im]
  unfold logVelocity
  field_simp [hn.ne', Real.exp_ne_zero _, (greenLogNormSq_pos κ q x).ne']

lemma sineGenerator_relative {p c r θ : ℝ} (hθ : 0 < Real.sin θ) :
    sineGenerator p r θ+c*sinePower r θ =
      sinePower r θ * ((r*(r-p)/2)*(1/Real.sin θ^2-1)+c-r/2) := by
  rw [sineGenerator_eq hθ]
  unfold sinePower
  rw [Real.rpow_sub hθ, Real.rpow_two]
  field_simp [hθ.ne']
  ring

theorem logFactor_generator_eq_angular (κ c r : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun q => logFactor κ c r q x) q)
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2 : ℝ)*iteratedDeriv 2 (logFactor κ c r q) x =
    κ*logVelocity κ q x^2*Real.exp ((c*κ/4)*(q.2-q.1.im))*
      (sineGenerator (greenExponent κ) r (logAngle κ q x)+
        c*sinePower r (logAngle κ q x)) := by
  rw [logFactor_physical_generator κ c r hκ,
    sineGenerator_relative (logAngle_sin_pos κ q x), logAngle_sin_sq,
    logFactor_eq_angular]
  have hN := (greenLogNormSq_pos κ q x).ne'
  have hY := Real.exp_ne_zero (2*q.1.im)
  have he : Real.exp q.1.im^2 = Real.exp (2*q.1.im) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  unfold logVelocity
  rw [div_pow, he]
  field_simp [hN, hY]
  dsimp only [greenLogNormSq]
  ring_nf

end SLEExactGauge.Multipoint

end

end OAI

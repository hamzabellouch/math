import OAI.NumberTheory.CubicMoment.Estimates.HeckeUniformLogDerivative

namespace OAI

/-! Concrete height and conductor scales for the prime contour. -/
noncomputable section
namespace CubicFirstMoment

def primeContourHeight (X : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log X))
def primeContourSize (Q X : ℝ) : ℝ := 32*Q*primeContourHeight X
def primeContourDenominator (Q X : ℝ) : ℝ := Real.log Q+Real.sqrt (Real.log X)
def primeContourDecay : ℝ :=
  1/(64*(1+heckePairLogConstant)*(2+Real.log 32))

lemma primeContourHeight_ge_one (X : ℝ) : 1 ≤ primeContourHeight X := by
  exact Real.one_le_exp (Real.sqrt_nonneg _)

lemma primeContourDecay_pos : 0 < primeContourDecay := by
  have hC := heckePairLogConstant_pos
  have hl : 0 < Real.log 32 := Real.log_pos (by norm_num)
  unfold primeContourDecay
  positivity

lemma primeContourSize_log {Q X : ℝ} (hQ : 0 < Q) :
    Real.log (primeContourSize Q X)=Real.log 32+Real.log Q+Real.sqrt (Real.log X) := by
  unfold primeContourSize primeContourHeight
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul (by norm_num) hQ.ne',Real.log_exp]

lemma primeContourSize_bounds {Q X : ℝ} (hQ : 1 ≤ Q) :
    10 ≤ primeContourSize Q X ∧ Q ≤ primeContourSize Q X ∧
      4+2*(primeContourHeight X+3) ≤ primeContourSize Q X := by
  have ht := primeContourHeight_ge_one X
  have hprod : 32*primeContourHeight X ≤ primeContourSize Q X := by
    dsimp [primeContourSize]
    nlinarith
  constructor
  · linarith
  constructor
  · dsimp [primeContourSize]
    nlinarith
  · linarith

lemma primeContourDenominator_ge_one {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    1 ≤ primeContourDenominator Q X := by
  have hroot : 1 ≤ Real.sqrt (Real.log X) := by
    exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hX)
  unfold primeContourDenominator
  linarith [Real.log_nonneg hQ]

lemma primeContourSize_log_bound {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    1+Real.log (primeContourSize Q X) ≤
      (2+Real.log 32)*primeContourDenominator Q X := by
  rw [primeContourSize_log (by linarith)]
  have hd := primeContourDenominator_ge_one hQ hX
  have hl : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  unfold primeContourDenominator at *
  nlinarith

lemma primeContourWidth_lower {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    primeContourDecay/primeContourDenominator Q X ≤ heckeZeroFreeWidth (primeContourSize Q X)/2 := by
  have hd := primeContourDenominator_ge_one hQ hX
  have hu := (primeContourSize_bounds hQ (X := X)).1
  have hlu : 0 < Real.log (primeContourSize Q X) := Real.log_pos (by linarith)
  have hC := heckePairLogConstant_pos
  have hl : 0 < Real.log 32 := Real.log_pos (by norm_num)
  have hb := primeContourSize_log_bound hQ hX
  have hrec : 1/(64*(1+heckePairLogConstant)*((2+Real.log 32)*primeContourDenominator Q X)) ≤
      1/(64*(1+heckePairLogConstant)*(1+Real.log (primeContourSize Q X))) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  convert hrec using 1 <;> simp only [primeContourDecay,heckeZeroFreeWidth,div_div] <;> congr 1 <;> ring

lemma primeContour_shifted_power {Q X : ℝ} (hQ : 1 ≤ Q)
    (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2) ≤
      X*Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X) := by
  have hw := primeContourWidth_lower hQ hX
  have he : X*Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X)=
      Real.exp (Real.log X-primeContourDecay*Real.log X/primeContourDenominator Q X) := by
    rw [Real.exp_sub,Real.exp_log hXp]
    rw [show -primeContourDecay*Real.log X/primeContourDenominator Q X =
      -(primeContourDecay*Real.log X/primeContourDenominator Q X) by ring,Real.exp_neg]
    ring
  rw [he,Real.rpow_def_of_pos hXp]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hw (show 0 ≤ Real.log X by linarith)
  have hh' : primeContourDecay*Real.log X/primeContourDenominator Q X ≤
      heckeZeroFreeWidth (primeContourSize Q X)/2*Real.log X := by
    convert hh using 1
    ring
  nlinarith

lemma primeContour_right_power {X : ℝ} (hX : 0 < X) (hlog : Real.log X ≠ 0) :
    X^(1+1/Real.log X)=Real.exp 1*X := by
  rw [Real.rpow_def_of_pos hX]
  have he : Real.log X*(1+1/Real.log X)=1+Real.log X := by field_simp; ring
  rw [he,Real.exp_add,Real.exp_log hX]

end CubicFirstMoment

end

end OAI

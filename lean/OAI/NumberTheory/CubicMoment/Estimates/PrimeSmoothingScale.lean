import OAI.NumberTheory.CubicMoment.Estimates.HeckePrimeScales

namespace OAI

/-! Choosing a cutoff width after its finite derivative order is known.
The same exponential saving absorbs the cutoff cost and the contour tail. -/
noncomputable section
namespace CubicFirstMoment

def primeSmoothingRate (d : ℕ) : ℝ := min primeContourDecay 1/(2*((d:ℝ)+1))
def primeSmoothingParameter (d : ℕ) (Q X : ℝ) : ℝ :=
  Real.exp (primeSmoothingRate d*(Real.log X/primeContourDenominator Q X))

lemma primeSmoothingRate_pos (d : ℕ) : 0 < primeSmoothingRate d := by
  unfold primeSmoothingRate
  positivity [primeContourDecay_pos]

lemma primeSmoothingRate_bounds (d : ℕ) :
    ((d:ℝ)+1)*primeSmoothingRate d ≤ primeContourDecay ∧
    ((d:ℝ)+1)*primeSmoothingRate d ≤ 1/2 ∧ primeSmoothingRate d ≤ 1/2 := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  have he : ((d:ℝ)+1)*primeSmoothingRate d = min primeContourDecay 1/2 := by
    unfold primeSmoothingRate
    field_simp
  have hmin : 0 < min primeContourDecay 1 := lt_min primeContourDecay_pos zero_lt_one
  have hleft : min primeContourDecay 1/2 ≤ primeContourDecay := by
    have hh := min_le_left primeContourDecay 1
    linarith
  have hright : min primeContourDecay 1/2 ≤ 1/2 := by
    have hh := min_le_right primeContourDecay 1
    linarith
  refine ⟨he.trans_le hleft,he.trans_le hright,?_⟩
  have hc := primeSmoothingRate_pos d
  nlinarith [show (0:ℝ) ≤ d by positivity]

lemma primeContour_ratio_bounds {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    0 ≤ Real.log X/primeContourDenominator Q X ∧
    Real.log X/primeContourDenominator Q X ≤ Real.sqrt (Real.log X) ∧
    Real.log X/primeContourDenominator Q X ≤ Real.log X := by
  have hd := primeContourDenominator_ge_one hQ hX
  have hl : 0 ≤ Real.log X := by linarith
  refine ⟨div_nonneg hl (by linarith),?_,div_le_self hl hd⟩
  apply (div_le_iff₀ (by linarith : 0 < primeContourDenominator Q X)).mpr
  have hs := Real.sq_sqrt hl
  have hq := Real.log_nonneg hQ
  unfold primeContourDenominator
  nlinarith [Real.sqrt_nonneg (Real.log X)]

lemma primeSmoothingParameter_ge_one (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) : 1 ≤ primeSmoothingParameter d Q X := by
  apply Real.one_le_exp
  exact mul_nonneg (primeSmoothingRate_pos d).le (primeContour_ratio_bounds hQ hX).1

lemma primeSmoothing_absorbs_shift (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d*
      Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X) ≤
    Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  rw [primeSmoothingParameter,←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (primeSmoothingRate_bounds d).1
    (primeContour_ratio_bounds hQ hX).1
  simp only [div_eq_mul_inv] at *
  nlinarith only [hh]

lemma primeSmoothing_absorbs_tail (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d/primeContourHeight X^2 ≤
      Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  rw [primeSmoothingParameter,primeContourHeight,←Real.exp_nat_mul,←Real.exp_nat_mul,
    ←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (primeSmoothingRate_bounds d).2.1
    (primeContour_ratio_bounds hQ hX).1
  have hb := (primeContour_ratio_bounds hQ hX).2.1
  norm_num only [Nat.cast_ofNat] at *
  simp only [div_eq_mul_inv] at *
  nlinarith [Real.sqrt_nonneg (Real.log X)]

lemma primeSmoothing_absorbs_sqrt (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    Real.sqrt X ≤ X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  have hh := mul_le_mul_of_nonneg_right (primeSmoothingRate_bounds d).2.2
    (primeContour_ratio_bounds hQ hX).1
  have hb := (primeContour_ratio_bounds hQ hX).2.2
  have he : Real.sqrt X=Real.exp (Real.log X/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hXp]
    congr 1
    ring
  calc
    _ = Real.exp (Real.log X/2) := he
    _ ≤ Real.exp (Real.log X+-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv] at *
      nlinarith
    _ = _ := by rw [Real.exp_add,Real.exp_log hXp]

lemma primeSmoothing_inverse (d : ℕ) (Q X : ℝ) :
    X/primeSmoothingParameter d Q X =
      X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  rw [primeSmoothingParameter,div_eq_mul_inv,←Real.exp_neg]
  congr 2
  ring

end CubicFirstMoment

end

end OAI

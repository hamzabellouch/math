import OAI.NumberTheory.CubicMoment.Estimates.PrimeSmoothingScale

namespace OAI

/-! Elementary optimization of the actual smoothed prime contour bound.
The cutoff order is fixed before the conductor and the summation length. -/
noncomputable section
namespace CubicFirstMoment

lemma primeLogSize_bounds {Q X : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 1 ≤ Real.log X) :
    1 ≤ Real.log (X*Q) ∧ Real.log X ≤ Real.log (X*Q) ∧
    primeContourDenominator Q X ≤ Real.log (X*Q) := by
  have hq := Real.log_nonneg hQ
  have hs : Real.sqrt (Real.log X) ≤ Real.log X := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith,?_⟩
    nlinarith
  rw [Real.log_mul hXp.ne' (show Q ≠ 0 by linarith)]
  unfold primeContourDenominator
  exact ⟨by linarith,by linarith,by linarith⟩

lemma primeLogDerivative_polynomial {Q X : ℝ} (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hX : 1 ≤ Real.log X) :
    heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2 ≤
      (heckeLogSquaredConstant*(2+Real.log 32)^2)*(Real.log (X*Q))^2 := by
  have hu := (primeContourSize_bounds hQ (X := X)).1
  have hp := (primeLogSize_bounds hQ hXp hX).2.2
  have hlog32 : 0 ≤ 2+Real.log 32 := by positivity
  have hh := (primeContourSize_log_bound hQ hX).trans
    (mul_le_mul_of_nonneg_left hp hlog32)
  have hleft : 0 ≤ 1+Real.log (primeContourSize Q X) := by
    have := Real.log_nonneg (show 1 ≤ primeContourSize Q X by linarith)
    linarith
  have hsq := pow_le_pow_left₀ hleft hh 2
  have hm := mul_le_mul_of_nonneg_left hsq heckeLogSquaredConstant_pos.le
  convert hm using 1
  ring

lemma primeSmoothing_left_power (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d*X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2) ≤
      X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) := by
  calc
    _ ≤ primeSmoothingParameter d Q X^d*
        (X*Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X)) :=
      mul_le_mul_of_nonneg_left (primeContour_shifted_power hQ hXp hX)
        (pow_nonneg (le_trans zero_le_one (primeSmoothingParameter_ge_one d hQ hX)) d)
    _ = X*(primeSmoothingParameter d Q X^d*
        Real.exp (-primeContourDecay*Real.log X/primeContourDenominator Q X)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeSmoothing_absorbs_shift d hQ hX) hXp.le

lemma primeSmoothing_right_power (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    primeSmoothingParameter d Q X^d*X^(1+1/Real.log X)/primeContourHeight X^2 ≤
      Real.exp 1*(X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) := by
  calc
    _ = (Real.exp 1*X)*(primeSmoothingParameter d Q X^d/primeContourHeight X^2) := by
      rw [primeContour_right_power hXp (by linarith)]
      ring
    _ ≤ (Real.exp 1*X)*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X) :=
      mul_le_mul_of_nonneg_left (primeSmoothing_absorbs_tail d hQ hX) (by positivity)
    _ = _ := by ring

lemma primeContour_optimized_bound (d : ℕ) {K C Q X : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    6*(K*primeSmoothingParameter d Q X^d)*
      (X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2)*
          (heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2)+
        X^(1+1/Real.log X)*(heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2+
          (1/((1+1/Real.log X)-1)+C))/primeContourHeight X^2) ≤
    (6*K*((1+Real.exp 1)*(heckeLogSquaredConstant*(2+Real.log 32)^2)+Real.exp 1*(1+C)))*
      (X*(Real.log (X*Q))^2*
        Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) := by
  let B := heckeLogSquaredConstant*(1+Real.log (primeContourSize Q X))^2
  let P := (Real.log (X*Q))^2
  let E := heckeLogSquaredConstant*(2+Real.log 32)^2
  let V := X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)
  have hB : 0 ≤ B := by dsimp [B]; positivity [heckeLogSquaredConstant_pos]
  have hBP : B ≤ E*P := primeLogDerivative_polynomial hQ hXp hX
  have hP : 1 ≤ P := by
    have hp := (primeLogSize_bounds hQ hXp hX).1
    dsimp [P]
    nlinarith
  have hLP : Real.log X ≤ P := by
    have hp := (primeLogSize_bounds hQ hXp hX).2.1
    have hp1 := (primeLogSize_bounds hQ hXp hX).1
    dsimp [P]
    nlinarith
  have hBCP : B+(Real.log X+C) ≤ (E+1+C)*P := by
    nlinarith [mul_le_mul_of_nonneg_left hP hC]
  have hden : 1/((1+1/Real.log X)-1)=Real.log X := by field_simp; ring
  rw [hden]
  change 6*(K*primeSmoothingParameter d Q X^d)*
    (X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2)*B+
      X^(1+1/Real.log X)*(B+(Real.log X+C))/primeContourHeight X^2) ≤ _
  calc
    _ = 6*K*((primeSmoothingParameter d Q X^d*
          X^(1-heckeZeroFreeWidth (primeContourSize Q X)/2))*B+
        (primeSmoothingParameter d Q X^d*X^(1+1/Real.log X)/primeContourHeight X^2)*
          (B+(Real.log X+C))) := by ring
    _ ≤ 6*K*(V*B+(Real.exp 1*V)*(B+(Real.log X+C))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_right (primeSmoothing_left_power d hQ hXp hX) hB)
        (mul_le_mul_of_nonneg_right (primeSmoothing_right_power d hQ hXp hX) (by positivity))
    _ ≤ 6*K*(V*(E*P)+(Real.exp 1*V)*((E+1+C)*P)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hBP (by dsimp [V]; positivity))
        (mul_le_mul_of_nonneg_left hBCP (by dsimp [V]; positivity))
    _ = _ := by dsimp [V,E,P]; ring

lemma primeSmoothing_cutoff_error (d : ℕ) {Q X : ℝ}
    (hQ : 1 ≤ Q) (hXp : 0 < X) (hX : 1 ≤ Real.log X) :
    32*(X/primeSmoothingParameter d Q X+Real.sqrt X)*Real.log (6*X) ≤
      64*(1+Real.log 6)*(X*(Real.log (X*Q))^2*
        Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)) := by
  have hp1 := (primeLogSize_bounds hQ hXp hX).1
  have hLP := (primeLogSize_bounds hQ hXp hX).2.1
  have hp2 : 1 ≤ (Real.log (X*Q))^2 := by nlinarith
  have hL2 : Real.log X ≤ (Real.log (X*Q))^2 := by nlinarith
  have hlog6 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 6)
  have hlog : Real.log (6*X) ≤ (1+Real.log 6)*(Real.log (X*Q))^2 := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    nlinarith
  have hlog0 : 0 ≤ Real.log (6*X) := by
    rw [Real.log_mul (by norm_num) hXp.ne']
    linarith
  let V := X*Real.exp (-primeSmoothingRate d*Real.log X/primeContourDenominator Q X)
  calc
    _ ≤ 32*(V+V)*Real.log (6*X) := by
      apply mul_le_mul_of_nonneg_right _ hlog0
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (le_of_eq (primeSmoothing_inverse d Q X))
        (primeSmoothing_absorbs_sqrt d hQ hXp hX)
    _ = 64*V*Real.log (6*X) := by ring
    _ ≤ 64*V*((1+Real.log 6)*(Real.log (X*Q))^2) :=
      mul_le_mul_of_nonneg_left hlog (by dsimp [V]; positivity)
    _ = _ := by dsimp [V]; ring

end CubicFirstMoment

end

end OAI

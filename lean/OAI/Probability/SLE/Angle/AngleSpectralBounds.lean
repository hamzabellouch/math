import OAI.Probability.SLE.Angle.AngleEigenNorm

namespace OAI

/-! Quantitative bounds on the normalized polynomial kernel terms. The
coarse quadratic exponential envelope is enough at a fixed large time. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def angleSpectralFactor (κ : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  (angleEigenSquareNorm κ 0/angleEigenSquareNorm κ n)*
    (angleEigenPolynomial κ n).eval x*(angleEigenPolynomial κ n).eval y

lemma angleSpectralFactor_zero {κ : ℝ} (hκ : 0<κ) (x y : ℝ) :
    angleSpectralFactor κ 0 x y=1 := by
  simp [angleSpectralFactor,angleEigenPolynomial_zero,(angleEigenSquareNorm_zero_pos hκ).ne']

lemma angleSpectralFactor_bound {κ : ℝ} (hκ : 0<κ) (n : ℕ) {x y : ℝ}
    (hx : |x|≤1) (hy : |y|≤1) :
    |angleSpectralFactor κ n x y|≤(4*(κ+4)/κ)^n*((n:ℝ)+1)^(2*(n+1)) := by
  have hc : 0<κ/(4*(κ+4)) := by positivity
  have hn := angleEigenSquareNorm_pos hκ n
  have h0 := angleEigenSquareNorm_zero_pos hκ
  have hr : angleEigenSquareNorm κ 0/angleEigenSquareNorm κ n≤
      (4*(κ+4)/κ)^n := by
    have he : (4*(κ+4)/κ)^n=(1/(κ/(4*(κ+4))))^n := by
      congr 1
      field_simp
    rw [he,one_div_pow]
    apply (div_le_div_iff₀ hn (pow_pos hc n)).mpr
    simpa only [one_mul] using angleEigenSquareNorm_lower hκ n
  unfold angleSpectralFactor
  rw [abs_mul,abs_mul,abs_of_pos (div_pos h0 hn)]
  calc
    _ ≤ (4*(κ+4)/κ)^n*((n:ℝ)+1)^(n+1)*((n:ℝ)+1)^(n+1) :=
      mul_le_mul (mul_le_mul hr (angleEigenPolynomial_eval_abs_le hκ n hx)
        (abs_nonneg _) (by positivity)) (angleEigenPolynomial_eval_abs_le hκ n hy)
          (abs_nonneg _) (by positivity)
    _ = _ := by rw [mul_assoc,← pow_add]; congr 2; omega

lemma angleSpectralFactor_exp_bound {κ : ℝ} (hκ : 0<κ) {n : ℕ} (hn : 1≤n)
    {x y : ℝ} (hx : |x|≤1) (hy : |y|≤1) :
    |angleSpectralFactor κ n x y|≤
      Real.exp ((4+Real.log (4*(κ+4)/κ))*(n:ℝ)^2) := by
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hb : 1≤4*(κ+4)/κ := (le_div_iff₀ hκ).mpr (by linarith)
  have hb0 : 0<4*(κ+4)/κ := by positivity
  have hl := Real.log_nonneg hb
  have hnpos : 0<(n:ℝ)+1 := by positivity
  have hlog : Real.log ((n:ℝ)+1)≤(n:ℝ) := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos hnpos
  calc
    _ ≤ (4*(κ+4)/κ)^n*((n:ℝ)+1)^(2*(n+1)) := angleSpectralFactor_bound hκ n hx hy
    _ = Real.exp ((n:ℝ)*Real.log (4*(κ+4)/κ)+
        (2*((n:ℝ)+1))*Real.log ((n:ℝ)+1)) := by
      rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log hb0,
        show 2*((n:ℝ)+1)=((2*(n+1):ℕ):ℝ) by push_cast; ring,
        Real.exp_nat_mul,Real.exp_log hnpos]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h1 : (2*((n:ℝ)+1))*Real.log ((n:ℝ)+1)≤(2*((n:ℝ)+1))*(n:ℝ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have h2 : (n:ℝ)*Real.log (4*(κ+4)/κ)≤(n:ℝ)^2*Real.log (4*(κ+4)/κ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hl
      nlinarith

end SLEExactGauge

end

end OAI

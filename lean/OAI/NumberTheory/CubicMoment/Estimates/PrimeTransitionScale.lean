import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeVariance

namespace OAI

/-! The diagonal and cube terms both give the required three-prime
logarithmic saving after Cauchy--Schwarz. -/
noncomputable section
namespace CubicFirstMoment

lemma transition_diagonal_scale {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≤ B^2) : A^2*B ≤ A^(5/3:ℝ)*B^(5/3:ℝ) := by
  have hh := Real.rpow_le_rpow hA.le hAB (show (0:ℝ) ≤ 1/3 by norm_num)
  rw [← Real.rpow_natCast B 2,← Real.rpow_mul hB.le] at hh
  norm_num at hh
  have ha : A^2 = A^(5/3:ℝ)*A^(1/3:ℝ) := by
    rw [← Real.rpow_add hA]; norm_num [Real.rpow_two]
  have hb : B^(5/3:ℝ) = B^(2/3:ℝ)*B := by
    calc
      _ = B^((2/3:ℝ)+1) := by norm_num
      _ = B^(2/3:ℝ)*B^((1:ℝ)) := Real.rpow_add hB _ _
      _ = _ := by rw [Real.rpow_one]
  rw [ha,hb,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hA.le _)
  exact mul_le_mul_of_nonneg_right (by simpa using hh) hB.le

lemma prime_transition_cauchy_scale {A B Z K M n : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hZ : 1 ≤ Z) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hAB : A ≤ B^2)
    (hn : n^2 ≤ (M*A/Z^2)*(K*(A*B/Z+A^(2/3:ℝ)*B^(5/3:ℝ)/Z^2))) :
    n ≤ Real.sqrt (2*M*K)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^(3/2:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hdiag := transition_diagonal_scale hA hB hAB
  have hpowA : A*A^(2/3:ℝ) = A^(5/3:ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one A]
    rw [← Real.rpow_add hA]; norm_num
  have hZ34 : Z^3 ≤ Z^4 := by nlinarith [pow_nonneg hZp.le 3]
  have hsplit : (M*A/Z^2)*(K*(A*B/Z+A^(2/3:ℝ)*B^(5/3:ℝ)/Z^2)) =
      (M*K)*(A^2*B)/Z^3+(M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^4 := by
    rw [← hpowA]
    field_simp
  have hs : n^2 ≤ (2*M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3 := by
    apply hn.trans
    rw [hsplit]
    calc
      _ ≤ (M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3+
          (M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3 := by
        apply add_le_add
        · gcongr
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hZ34
      _ = _ := by ring
  have hsquare : (Real.sqrt (2*M*K)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^(3/2:ℝ))^2 =
      (2*M*K)*(A^(5/3:ℝ)*B^(5/3:ℝ))/Z^3 := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (by positivity),
      ← Real.rpow_mul_natCast hA.le,← Real.rpow_mul_natCast hB.le,
      ← Real.rpow_mul_natCast hZp.le]
    norm_num [Real.rpow_natCast]
    ring
  have hnonneg : 0 ≤ Real.sqrt (2*M*K)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^(3/2:ℝ) := by positivity
  rw [← hsquare] at hs
  nlinarith

end CubicFirstMoment

end

end OAI

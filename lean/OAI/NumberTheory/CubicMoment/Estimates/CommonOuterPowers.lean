import OAI.NumberTheory.CubicMoment.Estimates.CommonRemainderBound

namespace OAI

/-! The power saving supplied by a genuinely shortened common-factor
row. This step uses only the scale inequalities of the application. -/
noncomputable section
namespace CubicFirstMoment

lemma shortened_poisson_polynomial {L A N δ η : ℝ}
    (hL : 1 ≤ L) (hA : 0 < A) (hN : 0 ≤ N) (hδ : 0 < δ)
    (hηδ : η ≤ δ) (hAL : L^(1-η) ≤ A) (hNL : N ≤ L^(1-δ)) :
    N+A^(1/3:ℝ)*N+A^(2/3:ℝ)*N^(2/3:ℝ) ≤
      3*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/3) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hfactor : L^(2/3:ℝ)*L^(-δ/3) = L^(2/3-δ/3) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have hA2 : L^((1-η)*(2/3:ℝ)) ≤ A^(2/3:ℝ) := by
    rw [Real.rpow_mul hLp.le]
    exact Real.rpow_le_rpow (by positivity) hAL (by norm_num)
  have hA1 : L^((1-η)*(1/3:ℝ)) ≤ A^(1/3:ℝ) := by
    rw [Real.rpow_mul hLp.le]
    exact Real.rpow_le_rpow (by positivity) hAL (by norm_num)
  have h1 : N ≤ A^(2/3:ℝ)*L^(2/3-δ/3) := by
    calc
      _ ≤ L^((1-η)*(2/3:ℝ)+(2/3-δ/3)) := hNL.trans
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
      _ = L^((1-η)*(2/3:ℝ))*L^(2/3-δ/3) := Real.rpow_add hLp _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hA2 (by positivity)
  have h2' : N ≤ A^(1/3:ℝ)*L^(2/3-δ/3) := by
    calc
      _ ≤ L^((1-η)*(1/3:ℝ)+(2/3-δ/3)) := hNL.trans
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
      _ = L^((1-η)*(1/3:ℝ))*L^(2/3-δ/3) := Real.rpow_add hLp _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hA1 (by positivity)
  have h2 : A^(1/3:ℝ)*N ≤ A^(2/3:ℝ)*L^(2/3-δ/3) := by
    have hh := mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg hA.le (1/3))
    have he : A^(1/3:ℝ)*A^(1/3:ℝ) = A^(2/3:ℝ) := by
      rw [← Real.rpow_add hA]; norm_num
    simpa only [← mul_assoc,he] using hh
  have h3 : A^(2/3:ℝ)*N^(2/3:ℝ) ≤ A^(2/3:ℝ)*L^(2/3-δ/3) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (L^(1-δ))^(2/3:ℝ) := Real.rpow_le_rpow hN hNL (by norm_num)
      _ = L^((1-δ)*(2/3:ℝ)) := (Real.rpow_mul hLp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  rw [mul_assoc (3*A^(2/3:ℝ)),hfactor]
  linarith

lemma common_outer_scale_small_power {B Q L A δ : ℝ}
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQL : Q ≤ L) (hL : 1 ≤ L)
    (hA : 1 ≤ A) (hδ : 0 < δ) :
    (B*Q^2*L^3/A)^(δ/100) ≤ B^(δ/100)*L^(δ/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hP : B*Q^2*L^3/A ≤ B*L^5 := by
    calc
      _ ≤ B*Q^2*L^3 := div_le_self (by positivity) hA
      _ ≤ B*L^2*L^3 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ hQL 2) hB) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (B*L^5)^(δ/100) := Real.rpow_le_rpow (by positivity) hP (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hB (by positivity),← Real.rpow_natCast L 5,← Real.rpow_mul hLp.le]
      congr 2
      norm_num
      ring

lemma commonOuterCost_power_saving (W : ℝ → ℂ) {C B Q A L δ η : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQL : Q ≤ L)
    (hL : 1 ≤ L) (hA : 0 < A) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hηδ : η ≤ δ) (hAL : L^(1-η) ≤ A) :
    commonOuterCost W C (δ/100) B Q A L (L^δ) ≤
      (‖normProfileFourier W 0‖/9)*A+
        3*C*B^(δ/100)*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/4) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA1 : 1 ≤ A := (Real.one_le_rpow hL (by linarith : 0 ≤ 1-η)).trans hAL
  have hmax : max 1 (L/L^δ) = L^(1-δ) := by
    have he : L/L^δ = L^(1-δ) := by rw [Real.rpow_sub hLp,Real.rpow_one]
    rw [he]
    exact max_eq_right (Real.one_le_rpow hL (by linarith))
  unfold commonOuterCost
  rw [hmax]
  apply add_le_add le_rfl
  have hp := common_outer_scale_small_power hB hQ hQL hL hA1 hδ
  have hb := shortened_poisson_polynomial hL hA (by positivity) hδ hηδ hAL le_rfl
  calc
    _ ≤ C*(B^(δ/100)*L^(δ/20))*(3*A^(2/3:ℝ)*L^(2/3:ℝ)*L^(-δ/3)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hC) hb (by positivity) (by positivity)
    _ = (3*C*B^(δ/100)*A^(2/3:ℝ)*L^(2/3:ℝ))*L^(δ/20-δ/3) := by
      rw [Real.rpow_sub hLp,show -δ/3 = -(δ/3) by ring,Real.rpow_neg hLp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

end CubicFirstMoment

end

end OAI

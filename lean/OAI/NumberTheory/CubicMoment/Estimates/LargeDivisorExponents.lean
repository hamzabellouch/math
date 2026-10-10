import OAI.NumberTheory.CubicMoment.Estimates.OuterSievePowers

namespace OAI

/-! A fixed positive power saving after shortening a rough common
prime divisor. Only the exponents needed for the dispersion application
are recorded. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_benchmark_factorization {B N : ℝ} (hB : 0 < B) (hN : 0 ≤ N) :
    B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N =
      B^(1/3:ℝ)*(B^(2/3:ℝ)+B^(1/3:ℝ)*N^(2/3:ℝ)+N) := by
  rw [Real.mul_rpow hB.le hN]
  have h₁ : B^(1/3:ℝ)*B^(2/3:ℝ) = B := by rw [← Real.rpow_add hB]; norm_num
  have h₂ : B^(1/3:ℝ)*B^(1/3:ℝ) = B^(2/3:ℝ) := by
    rw [← Real.rpow_add hB]
    norm_num
  rw [mul_add,mul_add,← mul_assoc,h₁,h₂]

lemma shortened_outer_polynomial {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ 1/4) (hηδ : η ≤ δ/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    B^(2/3:ℝ)+B^(1/3:ℝ)*N^(2/3:ℝ)+N ≤
      (1+A^(2/3:ℝ)+A)*L^(1-δ/8) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hB₂ : B^(2/3:ℝ) ≤ L^(1-δ/8) := by
    calc
      _ ≤ (L^(1+η))^(2/3:ℝ) := Real.rpow_le_rpow hB hBL (by norm_num)
      _ = L^((1+η)*(2/3:ℝ)) := (Real.rpow_mul hLp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by nlinarith)
  have hBN : B^(1/3:ℝ)*N^(2/3:ℝ) ≤ A^(2/3:ℝ)*L^(1-δ/8) := by
    calc
      _ ≤ (L^(1+η))^(1/3:ℝ)*(A*L^(1-δ))^(2/3:ℝ) :=
        mul_le_mul (Real.rpow_le_rpow hB hBL (by norm_num))
          (Real.rpow_le_rpow hN hNL (by norm_num))
          (Real.rpow_nonneg hN _) (Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _)
      _ = A^(2/3:ℝ)*L^((1+η)/3+(1-δ)*(2/3:ℝ)) := by
        rw [Real.mul_rpow hAp (Real.rpow_nonneg hLp.le _),
          ← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le]
        rw [show (1+η)*(1/3:ℝ) = (1+η)/3 by ring, Real.rpow_add hLp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (Real.rpow_nonneg hAp _)
  have hN' : N ≤ A*L^(1-δ/8) := hNL.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hAp)
  calc
    _ ≤ L^(1-δ/8)+A^(2/3:ℝ)*L^(1-δ/8)+A*L^(1-δ/8) :=
      add_le_add (add_le_add hB₂ hBN) hN'
    _ = _ := by ring

lemma shortened_outer_epsilon {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hη : η ≤ 1/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    (2*B*N)^(δ/100) ≤ (2*A)^(δ/100)*L^(3*δ/100) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hprod : 2*B*N ≤ (2*A)*L^3 := by
    calc
      _ ≤ 2*(L^(1+η))*(A*L^(1-δ)) := by gcongr
      _ = (2*A)*(L^(1+η)*L^(1-δ)) := by ring
      _ = (2*A)*L^((1+η)+(1-δ)) := by rw [← Real.rpow_add hLp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by rw [← Real.rpow_natCast L 3]; exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith))
        (by positivity)
  calc
    _ ≤ ((2*A)*L^3)^(δ/100) := Real.rpow_le_rpow (by positivity) hprod (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2*A) (by positivity : 0 ≤ L^3),
        ← Real.rpow_natCast L 3,← Real.rpow_mul hLp.le]
      congr 2
      ring

lemma shortened_outer_normalized_saving {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ 1/4) (hηδ : η ≤ δ/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    (2*B*N)^(δ/100)*(B^(2/3:ℝ)+B^(1/3:ℝ)*N^(2/3:ℝ)+N) ≤
      ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*L^(1-δ/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hpoly := shortened_outer_polynomial hL hB hN hA hδ hδ₁ hη hηδ hBL hNL
  have hpow := shortened_outer_epsilon hL hB hN hA hδ hη hBL hNL
  calc
    _ ≤ ((2*A)^(δ/100)*L^(3*δ/100))*
        ((1+A^(2/3:ℝ)+A)*L^(1-δ/8)) :=
      mul_le_mul hpow hpoly (by positivity) (by positivity)
    _ = ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*L^(3*δ/100+(1-δ/8)) := by
      rw [Real.rpow_add hLp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

lemma shortened_outer_power_saving {L B N A δ η : ℝ}
    (hL : 1 ≤ L) (hB : 0 < B) (hN : 0 ≤ N) (hA : 1 ≤ A)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hη : η ≤ 1/4) (hηδ : η ≤ δ/4)
    (hBL : B ≤ L^(1+η)) (hNL : N ≤ A*L^(1-δ)) :
    (2*B*N)^(δ/100)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*L ≤
      ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*L^2*B^(1/3:ℝ)*L^(-δ/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hs := mul_le_mul_of_nonneg_right
    (shortened_outer_normalized_saving hL hB.le hN hA hδ hδ₁ hη hηδ hBL hNL)
    (mul_nonneg (Real.rpow_nonneg hB.le (1/3:ℝ)) hLp.le)
  rw [outer_benchmark_factorization hB hN]
  convert hs using 1
  · ring
  · have he : L^(1-δ/20)*L = L^2*L^(-δ/20) := by
      rw [Real.rpow_sub hLp,Real.rpow_one,
        show -δ/20 = -(δ/20) by ring, Real.rpow_neg hLp.le]
      ring
    calc
      _ = ((2*A)^(δ/100)*(1+A^(2/3:ℝ)+A))*B^(1/3:ℝ)*(L^2*L^(-δ/20)) := by ring
      _ = _ := by rw [← he]; ring

end CubicFirstMoment

end

end OAI

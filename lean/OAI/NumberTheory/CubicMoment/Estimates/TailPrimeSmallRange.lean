import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeMiddleRange

namespace OAI

/-! Actual small prime groups meet the localized length range. Constants
from their fixed support widths are retained until a genuine exponent or
logarithmic margin absorbs them. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_tailPrime_small_localized_length {D K : ℝ} (hD : 0 < D) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ, 0 < B → X/D ≤ A*B →
      B ≤ X^(39/100:ℝ) → K*B^(3/2:ℝ) ≤ A := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (show (39/40:ℝ) < 1 by norm_num) (D*K)]
    with X hX hgap
  intro A B hB hAB hBX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hpow : B^(5/2:ℝ) ≤ X^(39/40:ℝ) := by
    calc
      _ ≤ (X^(39/100:ℝ))^(5/2:ℝ) :=
        Real.rpow_le_rpow hB.le hBX (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hXp.le]; norm_num
  have hprod : D*(B*(K*B^(3/2:ℝ))) ≤ D*(A*B) := by
    calc
      _ = (D*K)*B^(5/2:ℝ) := by
        have he : B*B^(3/2:ℝ) = B^(5/2:ℝ) := by
          calc
            _ = B^(1:ℝ)*B^(3/2:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [←Real.rpow_add hB]; norm_num
        calc
          _ = (D*K)*(B*B^(3/2:ℝ)) := by ring
          _ = _ := by rw [he]
      _ ≤ (D*K)*X^(39/40:ℝ) := mul_le_mul_of_nonneg_left hpow (mul_pos hD hK).le
      _ ≤ X := by simpa only [Real.rpow_one] using hgap
      _ ≤ D*(A*B) := by
        have hh := (div_le_iff₀ hD).mp hAB
        nlinarith
  have he : D*B*(K*B^(3/2:ℝ)) ≤ D*B*A := by nlinarith [hprod]
  exact (mul_le_mul_iff_right₀ (mul_pos hD hB)).mp he


lemma tailPrime_low_upper_of_constant {X A B c Q L : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hc : 0 < c)
    (hAB : A*B ≤ 3*X) (hBlo : c*X^(1/3:ℝ) ≤ B)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hmargin : 3*Q ≤ c^3*L^3) :
    Q*A ≤ B^2*L^3 := by
  have hcX := pow_le_pow_left₀ (by positivity : 0 ≤ c*X^(1/3:ℝ)) hBlo 3
  rw [mul_pow,←Real.rpow_mul_natCast hX.le] at hcX
  norm_num at hcX
  apply (mul_le_mul_iff_left₀ hB).mp
  calc
    Q*A*B ≤ (3*Q)*X := by nlinarith only [mul_le_mul_of_nonneg_left hAB hQ]
    _ ≤ (c^3*L^3)*X := mul_le_mul_of_nonneg_right hmargin hX.le
    _ = (c^3*X)*L^3 := by ring
    _ ≤ B^3*L^3 := mul_le_mul_of_nonneg_right hcX (by positivity)
    _ = B^2*L^3*B := by ring

theorem eventually_tailPrime_small_low_upper {c Q : ℝ} (hc : 0 < c) (hQ : 0 ≤ Q) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      c*X^(1/3:ℝ) ≤ B → A*B ≤ 3*X → Q*A ≤ B^2*(1+Real.log B)^3 := by
  have hnorm : Tendsto (fun X : ℝ => c*X^(1/3:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul_atTop hc
  filter_upwards [eventually_gt_atTop (0:ℝ),
    hnorm.eventually_ge_atTop (Real.exp (max 1 (3*Q/c^3)))] with X hX hlarge
  intro A B hBlo hAB
  have hBexp := hlarge.trans hBlo
  have hB : 0 < B := (Real.exp_pos _).trans_le hBexp
  have hlog : max 1 (3*Q/c^3) ≤ Real.log B := by
    simpa using Real.log_le_log (Real.exp_pos _) hBexp
  have hL : 1 ≤ 1+Real.log B := by linarith [le_max_left (1:ℝ) (3*Q/c^3)]
  have hpow : 1+Real.log B ≤ (1+Real.log B)^3 := le_self_pow₀ hL (by norm_num : 3 ≠ 0)
  have hmargin : 3*Q ≤ c^3*(1+Real.log B)^3 := by
    have ht : 3*Q/c^3 ≤ (1+Real.log B)^3 := by
      linarith [le_max_right (1:ℝ) (3*Q/c^3)]
    have hh := (div_le_iff₀ (pow_pos hc 3)).mp ht
    nlinarith only [hh]
  exact tailPrime_low_upper_of_constant hX hB hc hAB hBlo (zero_le_one.trans hL) hQ hmargin

theorem eventually_tailPrime_small_high_upper {κ γ Q : ℝ} (hκ : 0 < κ)
    (hκsmall : κ < 1/12) (hQ : 0 < Q)
    (hmargin : 1 < (1/3-3*κ)*(3+γ)) :
    ∀ᶠ X : ℝ in atTop, ∀ A B : ℝ,
      X^(1/3-3*κ) ≤ B → A*B ≤ 3*X → Q*A ≤ B^(2+γ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le hmargin (3*Q)] with X hX hgap
  intro A B hBlo hAB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hBp : 0 < B := (Real.rpow_pos_of_pos hXp _).trans_le hBlo
  have hexp : 0 ≤ 3+γ := by
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1/3-3*κ) (le_of_not_ge hh)
    linarith
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hBlo hexp
  rw [←Real.rpow_mul hXp.le] at hp
  have htop : 3*Q*X ≤ B^(3+γ) := by
    simpa only [Real.rpow_one] using hgap.trans hp
  apply (mul_le_mul_iff_left₀ hBp).mp
  calc
    Q*A*B ≤ 3*Q*X := by nlinarith only [mul_le_mul_of_nonneg_left hAB hQ.le]
    _ ≤ B^(3+γ) := htop
    _ = B^(2+γ)*B := by
      calc
        _ = B^((2+γ)+1) := by congr 1; ring
        _ = B^(2+γ)*B^((1:ℝ)) := Real.rpow_add hBp _ _
        _ = _ := by rw [Real.rpow_one]

end CubicFirstMoment

end

end OAI

import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

theorem log_sq_le_ratio_penalty {t : ℝ} (ht : 0<t) :
    (Real.log t)^2 ≤ t+t⁻¹-2 := by
  let x := Real.log t/2
  have hsq : x^2 ≤ (Real.sinh x)^2 := by
    by_cases hx : 0≤x
    · have h1 := Real.self_le_sinh_iff.mpr hx
      have h2 := Real.sinh_nonneg_iff.mpr hx
      nlinarith
    · have h1 := Real.sinh_le_self_iff.mpr (le_of_not_ge hx)
      have h2 := Real.sinh_nonpos_iff.mpr (le_of_not_ge hx)
      nlinarith
  have hc := Real.cosh_two_mul x
  have hi := Real.cosh_sq_sub_sinh_sq x
  have hx : 2*x=Real.log t := by dsimp [x]; ring
  rw [hx,Real.cosh_eq,Real.exp_log ht,Real.exp_neg,Real.exp_log ht] at hc
  dsimp [x] at hsq
  nlinarith

theorem ratio_penalty_nonneg {t : ℝ} (ht : 0<t) : 0≤t+t⁻¹-2 :=
  (sq_nonneg (Real.log t)).trans (log_sq_le_ratio_penalty ht)

theorem logRatio_cauchy (P : Finset ℕ) (κ : ℕ→ℝ)
    (hP : ∀p∈P,p.Prime) (hκ : ∀p∈P,0<κ p) :
    (∑ p∈P,abs (Real.log (κ p))/(p:ℝ))^2 ≤
      (∑ p∈P,(κ p+(κ p)⁻¹-2)*Real.log p/(p:ℝ)) *
      ∑ p∈P,1/((p:ℝ)*Real.log p) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro p hp
    exact div_nonneg (mul_nonneg (ratio_penalty_nonneg (hκ p hp))
      (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))) (Nat.cast_nonneg _)
  · intro p hp
    exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)))
  · intro p hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast (hP p hp).pos
    have hl : 0<Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (hP p hp).one_lt)
    have h := div_le_div_of_nonneg_right (log_sq_le_ratio_penalty (hκ p hp))
      (sq_nonneg (p:ℝ))
    rw [div_pow,sq_abs]
    calc
      _ ≤ (κ p+(κ p)⁻¹-2)/(p:ℝ)^2 := h
      _ = _ := by field_simp

end Ostmann.Supply

end

end OAI

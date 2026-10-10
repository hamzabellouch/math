import Mathlib

namespace OAI

section
section
open scoped BigOperators
noncomputable section
namespace Coulomb

lemma trial_kinetic_absorption {a M m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hM : m ≤ M) (hs : 1 ≤ a*m^(1/3:ℝ)) : M^(5/3:ℝ) ≤ a*M^2 := by
  have hM0 : 0 ≤ M := hm.trans hM
  have hsM : 1 ≤ a*M^(1/3:ℝ) := hs.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm hM (by norm_num)) ha)
  rcases eq_or_lt_of_le hM0 with h | h
  · simp [←h]
  · have he : M^(5/3:ℝ)*M^(1/3:ℝ) = M^2 := by
      rw [←Real.rpow_add h]
      norm_num
    calc
      M^(5/3:ℝ) ≤ M^(5/3:ℝ)*(a*M^(1/3:ℝ)) :=
        le_mul_of_one_le_right (Real.rpow_nonneg hM0 _) hsM
      _ = a*M^2 := by rw [←he]; ring

theorem positive_field_trial_optimization {E e a h C m : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hm : 0 ≤ m)
    (ham : 1 ≤ a*m) (ham' : 1 ≤ a*m^(1/3:ℝ))
    (htrial : ∀ M : ℝ, 0 ≤ M →
      E ≤ e-M*h+C*(M^(5/3:ℝ)/a^2+M/a^2+M^2/a)) :
    E ≤ e-a*(max h 0)^2/(16*C)+4*C*m^2/a := by
  have hE : E ≤ e := by simpa using htrial 0 (le_refl 0)
  have hp : 0 ≤ max h 0 := le_max_right _ _
  by_cases hh : a*max h 0 ≤ 8*C*m
  · have hs : (a*max h 0)^2 ≤ (8*C*m)^2 :=
      pow_le_pow_left₀ (mul_nonneg ha.le hp) hh 2
    have hg : a*(max h 0)^2/(16*C) ≤ 4*C*m^2/a := by
      apply (div_le_div_iff₀ (by positivity : 0 < 16*C) ha).2
      nlinarith [hs]
    linarith
  · have hh' : 8*C*m < a*max h 0 := lt_of_not_ge hh
    have hhp : 0 < h := by
      by_contra hn
      rw [max_eq_right (le_of_not_gt hn)] at hh'
      have : 0 ≤ 8*C*m := by positivity
      nlinarith
    rw [max_eq_left hhp.le] at hh' ⊢
    let M : ℝ := a*h/(8*C)
    have hM0 : 0 ≤ M := by dsimp [M]; positivity
    have hmM : m ≤ M := by
      apply (le_div_iff₀ (by positivity : 0 < 8*C)).2
      linarith
    have hk := trial_kinetic_absorption ha.le hm hmM ham'
    have hq : C*M^2/a = M*h/8 := by
      dsimp [M]
      field_simp
    have hscale : 8*C ≤ a^2*h := by
      have H := mul_le_mul_of_nonneg_left hh'.le ha.le
      have H' := mul_le_mul_of_nonneg_left ham (show 0 ≤ 8*C by positivity)
      nlinarith
    have hl : C*M/a^2 ≤ M*h/8 := by
      apply (div_le_div_iff₀ (by positivity : 0 < a^2) (by norm_num : (0:ℝ)<8)).2
      nlinarith [mul_le_mul_of_nonneg_left hscale hM0]
    have ht : C*(M^(5/3:ℝ)/a^2) ≤ M*h/8 := by
      calc
        _ ≤ C*(a*M^2/a^2) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hk (sq_nonneg a)) hC.le
        _ = C*M^2/a := by field_simp
        _ = M*h/8 := hq
    have hgain : M*h/2 = a*h^2/(16*C) := by dsimp [M]; ring
    have H := htrial M hM0
    have herr : 0 ≤ 4*C*m^2/a := by positivity
    have hMh : 0 ≤ M*h := mul_nonneg hM0 hhp.le
    rw [mul_add,mul_add] at H
    simp only [←mul_div_assoc] at H ht
    rw [hq] at H
    linarith

end Coulomb
end

end
end

end OAI

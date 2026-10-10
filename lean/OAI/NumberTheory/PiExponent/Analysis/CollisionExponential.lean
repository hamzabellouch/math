import OAI.NumberTheory.PiExponent.Analysis.CollisionCombinatorics

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

noncomputable def collisionRatio : ℝ := Real.exp (-Real.log 2 / 2)

theorem collisionRatio_pos : 0 < collisionRatio := Real.exp_pos _

theorem collisionRatio_lt_one : collisionRatio < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem collisionRatio_mul_self : collisionRatio * collisionRatio = 1 / 2 := by
  unfold collisionRatio
  rw [← Real.exp_add]
  have heq : -Real.log 2 / 2 + -Real.log 2 / 2 = -Real.log 2 := by ring
  rw [heq, Real.exp_neg, Real.exp_log (by norm_num)]
  simp only [one_div]

theorem factorial_le_exp_card_log (M : ℕ) :
    (M.factorial : ℝ) ≤ Real.exp ((M : ℝ) * Real.log M) := by
  by_cases hM : M = 0
  · subst M
    norm_num
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hM)]
    exact_mod_cast Nat.factorial_le_pow M

theorem twice_collision_count_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (group : ι → κ) :
    2 * ((∑ a, (multiplicity Finset.univ group a).choose 2 : ℕ) : ℝ) =
      (∑ a, (multiplicity Finset.univ group a : ℝ) ^ 2) - Fintype.card ι := by
  have hsum : (∑ a, (multiplicity Finset.univ group a : ℝ)) = Fintype.card ι := by
    exact_mod_cast sum_multiplicity_univ group
  push_cast
  rw [Finset.mul_sum]
  calc
    _ = ∑ a, ((multiplicity Finset.univ group a : ℝ) ^ 2 -
        (multiplicity Finset.univ group a : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Nat.cast_choose_two]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, hsum]

theorem collision_factor_le_exp (M C ell : ℕ) {H A v S : ℝ}
    (hell : (ell : ℝ) ≤ (M : ℝ) * H / v)
    (hC : 2 * (C : ℝ) = S - M) :
    ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
      collisionRatio ^ C * ((1 - collisionRatio)⁻¹) ^ M ≤
    Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v) +
      (M : ℝ) * (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio))) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hr : 0 < 1 - collisionRatio := sub_pos.mpr collisionRatio_lt_one
  have ht : (2 : ℝ) ^ ell ≤ Real.exp ((M : ℝ) * H / v * Real.log 2) := by
    calc
      _ = Real.exp ((ell : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hell hlog2)
  calc
    _ ≤ (Real.exp ((M : ℝ) * Real.log M) * (Real.exp (H * A)) ^ M *
        Real.exp ((M : ℝ) * H / v * Real.log 2)) *
        collisionRatio ^ C * ((1 - collisionRatio)⁻¹) ^ M := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hr.le) M)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg collisionRatio_pos.le C)
      apply mul_le_mul _ ht (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (factorial_le_exp_card_log M) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, collisionRatio, ← Real.exp_nat_mul]
      have hi : (1 - Real.exp (-Real.log 2 / 2))⁻¹ =
          Real.exp (-Real.log (1 - collisionRatio)) := by
        rw [Real.exp_neg, Real.exp_log hr]
        rfl
      rw [hi, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      have hc : (C : ℝ) = (S - M) / 2 := by linarith
      rw [hc]
      unfold collisionRatio
      ring

noncomputable def collisionRemainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio)) / H

theorem collision_factor_le_exp_normalized (M C ell : ℕ) {H A v S : ℝ}
    (hH : 0 < H) (hell : (ell : ℝ) ≤ (M : ℝ) * H / v)
    (hC : 2 * (C : ℝ) = S - M) :
    ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
      collisionRatio ^ C * ((1 - collisionRatio)⁻¹) ^ M ≤
    Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H *
      (A + Real.log 2 / v + collisionRemainder M H)) := by
  convert collision_factor_le_exp M C ell hell hC using 1
  congr 1
  unfold collisionRemainder
  field_simp
  ring

end PiExponent.Collision

end OAI

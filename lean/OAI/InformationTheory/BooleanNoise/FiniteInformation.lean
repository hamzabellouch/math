import OAI.InformationTheory.BooleanNoise.Statement

namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace LeanBlast.CourtadeKumar

theorem xlogx_mul (a b : ℝ) :
    xlogx (a * b) = a * xlogx b + b * xlogx a := by
  by_cases ha : a = 0
  · simp [ha, xlogx]
  by_cases hb : b = 0
  · simp [hb, xlogx]
  simp only [xlogx, Real.log_mul ha hb]
  ring

theorem finite_kl_eq_entropy_sums {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (j : A → B → ℝ) (hj : ∀ a b, 0 ≤ j a b) :
    (∑ a : A, ∑ b : B,
      if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      (∑ a : A, ∑ b : B, xlogx (j a b)) -
        (∑ a : A, xlogx (∑ b : B, j a b)) -
        (∑ b : B, xlogx (∑ a : A, j a b)) := by
  classical
  have hterm (a : A) (b : B) :
      (if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      xlogx (j a b) - j a b * Real.log (∑ z : B, j a z) -
        j a b * Real.log (∑ z : A, j z b) := by
    by_cases hp : 0 < j a b
    · have hr : 0 < ∑ z : B, j a z := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj a z) (Finset.mem_univ b))
      have hc : 0 < ∑ z : A, j z b := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj z b) (Finset.mem_univ a))
      rw [ite_eq_left hp, Real.log_div (ne_of_gt hp) (ne_of_gt (mul_pos hr hc)),
        Real.log_mul (ne_of_gt hr) (ne_of_gt hc)]
      unfold xlogx
      ring
    · have hz : j a b = 0 := le_antisymm (le_of_not_gt hp) (hj a b)
      simp [hz, xlogx]
  have hrow : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : B, j a z)) =
      ∑ a : A, xlogx (∑ b : B, j a b) := by
    simp only [xlogx, Finset.sum_mul]
  have hcol : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : A, j z b)) =
      ∑ b : B, xlogx (∑ a : A, j a b) := by
    rw [Finset.sum_comm]
    simp only [xlogx, Finset.sum_mul]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hrow, hcol]

end LeanBlast.CourtadeKumar

end

end OAI

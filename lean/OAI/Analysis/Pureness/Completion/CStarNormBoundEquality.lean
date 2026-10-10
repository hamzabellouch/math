import OAI.Analysis.Pureness.Completion.CStarAlgebraNorm
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI
noncomputable section
namespace CuntzPureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

theorem le_of_bound (p q : CStarAlgebraNorm R) (C : ℝ)
    (h : ∀ x, p.toAlgebraNorm x ≤ C * q.toAlgebraNorm x) (x : R) :
    p.toAlgebraNorm x ≤ q.toAlgebraNorm x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hqx : 0 < q.toAlgebraNorm x :=
    lt_of_le_of_ne (apply_nonneg q.toAlgebraNorm x)
      (Ne.symm (fun hz => hx (q.toAlgebraNorm.eq_zero_of_map_eq_zero' x hz)))
  have hpowers (k : ℕ) : ∃ z : R,
      p.toAlgebraNorm z = p.toAlgebraNorm x ^ (2^k) ∧
      q.toAlgebraNorm z = q.toAlgebraNorm x ^ (2^k) := by
    induction k with
    | zero => exact ⟨x, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨z, hpz, hqz⟩ := ih
      refine ⟨star z*z, ?_, ?_⟩
      · rw [p.cstar, hpz, pow_succ, pow_mul, pow_two]
      · rw [q.cstar, hqz, pow_succ, pow_mul, pow_two]
  by_contra hle
  have hr : 1 < p.toAlgebraNorm x / q.toAlgebraNorm x :=
    (one_lt_div hqx).mpr (lt_of_not_ge hle)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hr
  obtain ⟨z, hpz, hqz⟩ := hpowers k
  have hb := h z
  rw [hpz, hqz] at hb
  have hb' : (p.toAlgebraNorm x / q.toAlgebraNorm x) ^ (2^k) ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hqx _)).mpr hb
  exact (not_lt_of_ge ((pow_le_pow_right₀ hr.le (Nat.le_of_lt (Nat.lt_two_pow_self))).trans hb')) hk

theorem eq_of_mutual_bound (p q : CStarAlgebraNorm R)
    (hpq : ∃ C : ℝ, ∀ x, p.toAlgebraNorm x ≤ C*q.toAlgebraNorm x)
    (hqp : ∃ C : ℝ, ∀ x, q.toAlgebraNorm x ≤ C*p.toAlgebraNorm x) : p=q := by
  obtain ⟨C, hC⟩ := hpq
  obtain ⟨D, hD⟩ := hqp
  have he : p.toAlgebraNorm=q.toAlgebraNorm := AlgebraNorm.ext (fun x =>
    le_antisymm (le_of_bound p q C hC x) (le_of_bound q p D hD x))
  cases p
  cases q
  cases he
  rfl
end CuntzPureness.CStarAlgebraNorm

end

end OAI

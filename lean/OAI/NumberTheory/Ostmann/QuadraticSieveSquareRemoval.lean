import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve

theorem jacobi_square_mul_left (u v : ℤ) (q : ℕ) [NeZero q] :
    jacobiSym (u ^ 2 * v) q = if u.gcd (q : ℤ) = 1 then jacobiSym v q else 0 := by
  rw [jacobiSym.mul_left, jacobiSym.pow_left]
  by_cases h : u.gcd (q : ℤ) = 1
  · rw [ite_eq_left h, jacobiSym.sq_one h, one_mul]
  · rw [ite_eq_right h, jacobiSym.eq_zero_iff_not_coprime.mpr h]
    norm_num

theorem jacobi_square_mul_right (m : ℤ) (d q : ℕ) [NeZero d] [NeZero q] :
    jacobiSym m (d ^ 2 * q) = if m.gcd (d : ℤ) = 1 then jacobiSym m q else 0 := by
  rw [jacobiSym.mul_right' m (pow_ne_zero 2 (NeZero.ne d)) (NeZero.ne q),
    jacobiSym.pow_right]
  by_cases h : m.gcd (d : ℤ) = 1
  · rw [ite_eq_left h, jacobiSym.sq_one h, one_mul]
  · rw [ite_eq_right h, jacobiSym.eq_zero_iff_not_coprime.mpr h]
    norm_num

def gcdReducedModulus (n₁ n₂ : ℕ) : ℕ :=
  (n₁ / n₁.gcd n₂) * (n₂ / n₁.gcd n₂)

theorem mul_eq_gcd_sq_mul_reduced (n₁ n₂ : ℕ) :
    n₁ * n₂ = (n₁.gcd n₂) ^ 2 * gcdReducedModulus n₁ n₂ := by
  unfold gcdReducedModulus
  have h₁ := Nat.mul_div_cancel' (Nat.gcd_dvd_left n₁ n₂)
  have h₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right n₁ n₂)
  calc
    n₁ * n₂ = (n₁.gcd n₂ * (n₁ / n₁.gcd n₂)) *
        (n₁.gcd n₂ * (n₂ / n₁.gcd n₂)) := by rw [h₁, h₂]
    _ = _ := by ring

theorem jacobi_gcd_denominator (m : ℤ) (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] :
    jacobiSym m (n₁ * n₂) =
      if m.gcd (n₁.gcd n₂ : ℤ) = 1 then jacobiSym m (gcdReducedModulus n₁ n₂) else 0 := by
  have hd : n₁.gcd n₂ ≠ 0 := Nat.gcd_ne_zero_left (NeZero.ne n₁)
  have hprod : (n₁.gcd n₂) ^ 2 * gcdReducedModulus n₁ n₂ ≠ 0 := by
    rw [← mul_eq_gcd_sq_mul_reduced]
    exact mul_ne_zero (NeZero.ne n₁) (NeZero.ne n₂)
  have : NeZero (n₁.gcd n₂) := ⟨hd⟩
  have : NeZero (gcdReducedModulus n₁ n₂) := ⟨(mul_ne_zero_iff.mp hprod).2⟩
  rw [mul_eq_gcd_sq_mul_reduced]
  exact jacobi_square_mul_right m (n₁.gcd n₂) (gcdReducedModulus n₁ n₂)

theorem gcdReducedModulus_squarefree {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    Squarefree (gcdReducedModulus n₁ n₂) := by
  apply Nat.squarefree_mul_iff.mpr
  exact ⟨Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left h₁.ne_zero)),
    h₁.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂)),
    h₂.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n₁ n₂))⟩

end Ostmann.QuadraticSieve

end OAI

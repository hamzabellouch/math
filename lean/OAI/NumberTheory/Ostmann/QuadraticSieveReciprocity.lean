import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve

def reciprocityTwist (r s : ℕ) : ℤ :=
  if r % 4 = 3 then jacobiSym (-1) s else 1

theorem reciprocityTwist_eq_if (r : ℕ) {s : ℕ} (hs : Odd s) :
    reciprocityTwist r s = if r % 4 = 3 ∧ s % 4 = 3 then -1 else 1 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hs) with hs1 | hs3
  · simp [reciprocityTwist, jacobiSym.at_neg_one hs,
      ZMod.χ₄_nat_one_mod_four hs1, hs1]
  · simp [reciprocityTwist, jacobiSym.at_neg_one hs,
      ZMod.χ₄_nat_three_mod_four hs3, hs3]

theorem reciprocityTwist_congr_left {r v : ℕ} (h : r % 4 = v % 4) (s : ℕ) :
    reciprocityTwist r s = reciprocityTwist v s := by
  simp only [reciprocityTwist, h]

theorem reciprocityTwist_sq (r s : ℕ) : reciprocityTwist r s ^ 2 = 1 := by
  unfold reciprocityTwist
  split
  · exact jacobiSym.sq_one (by simp)
  · norm_num

theorem norm_mul_reciprocityTwist (z : ℂ) (r s : ℕ) :
    ‖z * (reciprocityTwist r s : ℂ)‖ = ‖z‖ := by
  have hsign : reciprocityTwist r s = 1 ∨ reciprocityTwist r s = -1 := by
    unfold reciprocityTwist
    split
    · exact jacobiSym.eq_one_or_neg_one (by simp)
    · exact Or.inl rfl
  rcases hsign with h | h <;> simp [h]

theorem norm_mul_jacobi_twist_le (z : ℂ) (c : ℤ) (r s : ℕ) :
    ‖z * (jacobiSym c s : ℂ) * (reciprocityTwist r s : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_mul_reciprocityTwist]
  rcases jacobiSym.trichotomy c s with h | h | h <;> simp [h]

theorem norm_mul_jacobi_twist_of_coprime (z : ℂ) (c : ℤ) (r s : ℕ)
    (hc : c.gcd (s : ℤ) = 1) :
    ‖z * (jacobiSym c s : ℂ) * (reciprocityTwist r s : ℂ)‖ = ‖z‖ := by
  rw [norm_mul_reciprocityTwist]
  rcases jacobiSym.eq_one_or_neg_one hc with h | h <;> simp [h]

theorem sum_norm_sq_jacobi_twist_le (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (r : ℕ) :
    (∑ s ∈ S, ‖a s * (jacobiSym c s : ℂ) * (reciprocityTwist r s : ℂ)‖ ^ 2) ≤
      ∑ s ∈ S, ‖a s‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro s hs
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_mul_jacobi_twist_le (a s) c r s) 2

theorem jacobi_reciprocity_twist {v s : ℕ} (hv : Odd v) (hs : Odd s) :
    jacobiSym (v : ℤ) s = reciprocityTwist v s * jacobiSym (s : ℤ) v := by
  rw [reciprocityTwist_eq_if v hs]
  simpa only [ite_mul, neg_one_mul, one_mul] using
    (jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp hv) (Nat.odd_iff.mp hs)).symm

theorem jacobi_reciprocity_twist_of_mod_four {r v s : ℕ}
    (hv : Odd v) (hs : Odd s) (hrv : r % 4 = v % 4) :
    jacobiSym (v : ℤ) s = reciprocityTwist r s * jacobiSym (s : ℤ) v := by
  rw [reciprocityTwist_congr_left hrv]
  exact jacobi_reciprocity_twist hv hs

theorem jacobi_mul_reciprocity_twist (c : ℤ) {r v s : ℕ}
    (hv : Odd v) (hs : Odd s) (hrv : r % 4 = v % 4) :
    jacobiSym (c * (v : ℤ)) s =
      (jacobiSym c s * reciprocityTwist r s) * jacobiSym (s : ℤ) v := by
  rw [jacobiSym.mul_left, jacobi_reciprocity_twist_of_mod_four hv hs hrv, mul_assoc]

theorem jacobi_neg_reciprocity_twist {r v s : ℕ}
    (hv : Odd v) (hs : Odd s) (hrv : r % 4 = v % 4) :
    jacobiSym (-(v : ℤ)) s =
      (ZMod.χ₄ s * reciprocityTwist r s) * jacobiSym (s : ℤ) v := by
  simpa only [neg_one_mul, jacobiSym.at_neg_one hs] using
    jacobi_mul_reciprocity_twist (-1) hv hs hrv

theorem jacobi_two_mul_reciprocity_twist {r v s : ℕ}
    (hv : Odd v) (hs : Odd s) (hrv : r % 4 = v % 4) :
    jacobiSym (2 * (v : ℤ)) s =
      (ZMod.χ₈ s * reciprocityTwist r s) * jacobiSym (s : ℤ) v := by
  simpa only [jacobiSym.at_two hs] using
    jacobi_mul_reciprocity_twist 2 hv hs hrv

theorem jacobi_neg_two_mul_reciprocity_twist {r v s : ℕ}
    (hv : Odd v) (hs : Odd s) (hrv : r % 4 = v % 4) :
    jacobiSym (-2 * (v : ℤ)) s =
      (ZMod.χ₈' s * reciprocityTwist r s) * jacobiSym (s : ℤ) v := by
  simpa only [jacobiSym.at_neg_two hs] using
    jacobi_mul_reciprocity_twist (-2) hv hs hrv

theorem sum_jacobi_mul_reciprocity_twist (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ)
    {r v : ℕ} (hv : Odd v) (hS : ∀ s ∈ S, Odd s) (hrv : r % 4 = v % 4) :
    (∑ s ∈ S, a s * (jacobiSym (c * (v : ℤ)) s : ℂ)) =
      ∑ s ∈ S, (a s * (jacobiSym c s : ℂ) * (reciprocityTwist r s : ℂ)) *
        (jacobiSym (s : ℤ) v : ℂ) := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [jacobi_mul_reciprocity_twist c hv (hS s hs) hrv]
  push_cast
  ring

end Ostmann.QuadraticSieve

end OAI

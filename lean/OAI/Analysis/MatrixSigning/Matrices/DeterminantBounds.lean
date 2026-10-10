import Mathlib

namespace OAI

section

namespace KS.W30

open Matrix

theorem factorial_le_two_pow_sq (n : ℕ) : n.factorial ≤ 2 ^ (n * n) := by
  calc
    n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) n
    _ = 2 ^ (n * n) := (pow_mul 2 n n).symm

theorem abs_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hA : ∀ i j, |A i j| ≤ (B : ℤ)) :
    |A.det| ≤ (n.factorial : ℤ) * (B : ℤ) ^ n := by
  simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hA)

theorem natAbs_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ B) :
    A.det.natAbs ≤ n.factorial * B ^ n := by
  have hh : ∀ i j, |A i j| ≤ (B : ℤ) := by
    intro i j
    rw [← Int.natCast_natAbs]
    exact_mod_cast hA i j
  have hd := abs_det_le A B hh
  rw [← Int.natCast_natAbs] at hd
  exact_mod_cast hd

theorem natAbs_det_le_two_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) :
    A.det.natAbs ≤ 2 ^ (n * n + b * n) := by
  calc
    A.det.natAbs ≤ n.factorial * (2 ^ b) ^ n := natAbs_det_le A (2 ^ b) hA
    _ ≤ 2 ^ (n * n) * (2 ^ b) ^ n :=
      Nat.mul_le_mul_right _ (factorial_le_two_pow_sq n)
    _ = 2 ^ (n * n + b * n) := by rw [← pow_mul, ← pow_add]

theorem size_natAbs_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) :
    Nat.size A.det.natAbs ≤ n * n + b * n + 1 := by
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt (natAbs_det_le_two_pow A b hA)
    (by
      rw [pow_succ]
      have hp : 0 < 2 ^ (n * n + b * n) := Nat.pow_pos (by decide)
      omega)

theorem abs_adjugate_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hB : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ (B : ℤ)) (i j : Fin n) :
    |A.adjugate i j| ≤ (n.factorial : ℤ) * (B : ℤ) ^ n := by
  rw [Matrix.adjugate_apply]
  apply abs_det_le
  intro k l
  by_cases hk : k = j
  · subst k
    by_cases hl : l = i
    · subst l
      simpa using (show (1 : ℤ) ≤ (B : ℤ) by exact_mod_cast hB)
    · simp [Matrix.updateRow, Function.update, hl]
  · simpa [Matrix.updateRow, Function.update, hk] using hA k l

theorem natAbs_adjugate_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hB : 1 ≤ B) (hA : ∀ i j, (A i j).natAbs ≤ B) (i j : Fin n) :
    (A.adjugate i j).natAbs ≤ n.factorial * B ^ n := by
  have hh : ∀ i j, |A i j| ≤ (B : ℤ) := by
    intro k l
    rw [← Int.natCast_natAbs]
    exact_mod_cast hA k l
  have hd := abs_adjugate_le A B hB hh i j
  rw [← Int.natCast_natAbs] at hd
  exact_mod_cast hd

theorem natAbs_adjugate_le_two_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) (i j : Fin n) :
    (A.adjugate i j).natAbs ≤ 2 ^ (n * n + b * n) := by
  calc
    (A.adjugate i j).natAbs ≤ n.factorial * (2 ^ b) ^ n :=
      natAbs_adjugate_le A (2 ^ b) (Nat.one_le_two_pow) hA i j
    _ ≤ 2 ^ (n * n) * (2 ^ b) ^ n :=
      Nat.mul_le_mul_right _ (factorial_le_two_pow_sq n)
    _ = 2 ^ (n * n + b * n) := by rw [← pow_mul, ← pow_add]

end KS.W30

end

end OAI

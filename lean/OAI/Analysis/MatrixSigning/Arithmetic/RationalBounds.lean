import Mathlib

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem divInt_num_natAbs_le (a b : ℤ) (hb : b ≠ 0) :
    (a /. b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha

theorem divInt_den_le (a b : ℤ) (hb : b ≠ 0) :
    (a /. b).den ≤ b.natAbs := by
  simpa using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

theorem divInt_num_size_le (a b : ℤ) (hb : b ≠ 0) (k : ℕ)
    (ha : a.natAbs < 2 ^ k) : Nat.size (a /. b).num.natAbs ≤ k := by
  exact Nat.size_le.mpr (lt_of_le_of_lt (divInt_num_natAbs_le a b hb) ha)

theorem divInt_den_size_le (a b : ℤ) (hb : b ≠ 0) (k : ℕ)
    (hsize : b.natAbs < 2 ^ k) : Nat.size (a /. b).den ≤ k := by
  exact Nat.size_le.mpr (lt_of_le_of_lt (divInt_den_le a b hb) hsize)

theorem matrix_den_dvd_prod {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.den ∣ ∏ p : Fin m × Fin n, (A p.1 p.2).den := by
  apply Matrix.den_dvd_iff.mpr
  intro i j
  exact Finset.dvd_prod_of_mem (fun p : Fin m × Fin n => (A p.1 p.2).den)
    (Finset.mem_univ (i, j))

theorem matrix_den_le_prod {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    A.den ≤ ∏ p : Fin m × Fin n, (A p.1 p.2).den := by
  apply Nat.le_of_dvd _ (matrix_den_dvd_prod A)
  apply Finset.prod_pos
  intro p _
  exact Nat.pos_of_ne_zero (A p.1 p.2).den_nz

theorem matrix_den_le_two_pow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : ℕ)
    (hA : ∀ i j, (A i j).den ≤ 2 ^ b) :
    A.den ≤ 2 ^ (b * (m * n)) := by
  calc
    A.den ≤ ∏ p : Fin m × Fin n, (A p.1 p.2).den := matrix_den_le_prod A
    _ ≤ ∏ _p : Fin m × Fin n, 2 ^ b := by
      exact Finset.prod_le_prod (fun entry _ => hA entry.1 entry.2)
    _ = 2 ^ (b * (m * n)) := by simp [← pow_mul]

theorem cleared_matrix_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) :
    (A.num i j : ℚ) = (A.den : ℚ) * A i j := by
  have h := Matrix.num_div_den A i j
  apply (div_eq_iff (Nat.cast_ne_zero.mpr A.den_ne_zero)).mp at h
  simpa [mul_comm] using h

theorem cleared_num_natAbs_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) :
    (A.num i j).natAbs ≤ A.den * (A i j).num.natAbs := by
  obtain ⟨k, hk⟩ := Matrix.den_dvd_iff.mp (dvd_refl A.den) i j
  have heq : A.num i j = (k : ℤ) * (A i j).num := by
    have hc : (A.num i j : ℚ) = (((k : ℤ) * (A i j).num : ℤ) : ℚ) := by
      rw [cleared_matrix_entry, hk, Nat.cast_mul]
      calc
        ((A i j).den : ℚ) * k * A i j = (k : ℚ) * ((A i j).den * A i j) := by ring
        _ = (k : ℚ) * (A i j).num := by rw [Rat.den_mul_eq_num]
        _ = (((k : ℤ) * (A i j).num : ℤ) : ℚ) := by simp
    exact_mod_cast hc
  have hk_le : k ≤ A.den := by
    rw [hk]
    exact Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero (A i j).den_nz)
  rw [heq, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_right _ hk_le

theorem cleared_num_le_two_pow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : ℕ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b) (i : Fin m) (j : Fin n) :
    (A.num i j).natAbs ≤ 2 ^ (b * (m * n) + b) := by
  calc
    (A.num i j).natAbs ≤ A.den * (A i j).num.natAbs := cleared_num_natAbs_le A i j
    _ ≤ 2 ^ (b * (m * n)) * 2 ^ b :=
      Nat.mul_le_mul (matrix_den_le_two_pow A b hden) (hnum i j)
    _ = 2 ^ (b * (m * n) + b) := (pow_add 2 _ _).symm

end KS.W30

end

end OAI

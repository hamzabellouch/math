import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

def rightJacobi (n m : ℕ) : ℤ := if Odd m then jacobiSym (n : ℤ) m else 0

theorem rightJacobi_mod (n m : ℕ) : rightJacobi n m = rightJacobi n (m % (4 * n)) := by
  have hodd : Odd (m % (4 * n)) ↔ Odd m := by
    rw [Nat.odd_iff, Nat.odd_iff, Nat.mod_mod_of_dvd]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) n
  by_cases hm : Odd m
  · simp only [rightJacobi, hm, hodd.mpr hm, ite_eq_left]
    exact jacobiSym.mod_right' n hm
  · simp [rightJacobi, hm, hodd]

theorem rightJacobi_periodic (n : ℕ) : Function.Periodic (rightJacobi n) (4 * n) := by
  intro m
  rw [rightJacobi_mod n (m + 4 * n), Nat.add_mod_right, ← rightJacobi_mod]

@[simp] theorem rightJacobi_one (n : ℕ) : rightJacobi n 1 = 1 := by
  simp [rightJacobi]

@[simp] theorem rightJacobi_zero (n : ℕ) : rightJacobi n 0 = 0 := by
  simp [rightJacobi]

theorem rightJacobi_mul (n a b : ℕ) :
    rightJacobi n (a * b) = rightJacobi n a * rightJacobi n b := by
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · simp only [rightJacobi, ha, hb, ha.mul hb, ite_eq_left]
      exact jacobiSym.mul_right' _ (by rintro rfl; simp at ha) (by rintro rfl; simp at hb)
    · have hab : ¬ Odd (a * b) := by simpa [Nat.odd_mul, ha] using hb
      simp [rightJacobi, hab, hb]
  · have hab : ¬ Odd (a * b) := by simp [Nat.odd_mul, ha]
    simp [rightJacobi, hab, ha]

theorem rightJacobi_abs_le_one (n m : ℕ) : |rightJacobi n m| ≤ 1 := by
  unfold rightJacobi
  split_ifs with hm
  · rcases jacobiSym.trichotomy (n : ℤ) m with h | h | h <;> simp [h]
  · norm_num

end Ostmann.QuadraticCenter

end OAI

import Mathlib

namespace OAI

/-! Elementary degree and divisibility bounds for chromatic sphere products. -/

namespace SphereKernelArithmetic

def stemDegree (p : ℕ) : ℕ := 2 * p * (p - 1) - 2

def powerExponent (p : ℕ) : ℕ := (p - 1) ^ 2

theorem stemDegree_pos_even (p : ℕ) (hp : 7 ≤ p) :
    0 < stemDegree p ∧ Even (stemDegree p) := by
  have h1 : 1 ≤ p - 1 := by omega
  have hprod : 1 < p * (p - 1) := by nlinarith
  have hdegree : stemDegree p = 2 * (p * (p - 1) - 1) := by
    dsimp only [stemDegree]
    calc
      2 * p * (p - 1) - 2 = 2 * (p * (p - 1)) - 2 * 1 := by
        rw [mul_assoc, mul_one]
      _ = 2 * (p * (p - 1) - 1) := (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdegree]
  constructor
  · omega
  · exact even_two_mul _

theorem upper_height_margin (p : ℕ) (hp : 7 ≤ p) :
    2 * powerExponent p = ((p + 1) ^ 2 + 1) + p * (p - 6) ∧
      (p + 1) ^ 2 + 2 ≤ 2 * powerExponent p := by
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have h6 : p - 6 + 6 = p := Nat.sub_add_cancel (by omega)
  have heq : 2 * powerExponent p = ((p + 1) ^ 2 + 1) + p * (p - 6) := by
    dsimp only [powerExponent]
    nlinarith
  refine ⟨heq, ?_⟩
  have hm : 0 < p * (p - 6) := Nat.mul_pos (by omega) (by omega)
  omega

theorem not_dvd_upper_dimension (p : ℕ) (hp : 7 ≤ p) :
    ¬ (p - 1) ∣ (p + 1) ^ 2 := by
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have heq : (p + 1) ^ 2 = (p - 1) * (p + 3) + 4 := by nlinarith
  intro hd
  rw [heq] at hd
  have hfour : p - 1 ∣ 4 :=
    (Nat.dvd_add_iff_right (dvd_mul_right (p - 1) (p + 3))).mpr hd
  have hle : p - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hfour
  omega

end SphereKernelArithmetic

end OAI

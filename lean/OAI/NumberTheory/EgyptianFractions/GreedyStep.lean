import Mathlib

namespace OAI
noncomputable section
namespace Problem337

/-- Arithmetic data for one step of the greedy Egyptian fraction algorithm. -/
theorem greedy_step_data (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hr : b % a ≠ 0) :
    ∃ z c : ℕ, 2 ≤ z ∧ 0 < c ∧ c < a ∧ c < b * z ∧
      (a : ℚ) / b = 1 / (z : ℚ) + (c : ℚ) / (b * z : ℕ) ∧
      (c : ℚ) / (b * z : ℕ) < 1 / (z : ℚ) := by
  let z := b / a + 1
  let c := a - b % a
  have hmod : b % a < a := Nat.mod_lt b ha
  have hquot : 1 ≤ b / a := Nat.one_le_div_iff ha |>.2 (by omega)
  have hz : 2 ≤ z := by dsimp [z]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hca : c < a := by dsimp [c]; omega
  have hcb : c < b := lt_trans hca hab
  have heq : a * z = b + c := by
    have hd := Nat.mod_add_div b a
    dsimp [z, c]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hcz : c < b * z := by nlinarith
  have hbq : (0 : ℚ) < b := by exact_mod_cast (lt_trans ha hab)
  have hzq : (0 : ℚ) < z := by exact_mod_cast (by omega : 0 < z)
  have heqq : (a : ℚ) * z = b + c := by exact_mod_cast heq
  refine ⟨z, c, hz, hc, hca, hcz, ?_, ?_⟩
  · push_cast
    field_simp
    nlinarith
  · push_cast
    apply (div_lt_div_iff₀ (mul_pos hbq hzq) hzq).2
    have hcbq : (c : ℚ) < b := by exact_mod_cast hcb
    nlinarith

/-- The terminal, divisible case of the greedy algorithm. -/
theorem greedy_terminal_data (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hr : b % a = 0) :
    2 ≤ b / a ∧ (a : ℚ) / b = 1 / (b / a : ℕ) := by
  have hd : a * (b / a) = b := by
    have h := Nat.mod_add_div b a
    omega
  have hq : 2 ≤ b / a := by
    by_contra h
    have : b / a ≤ 1 := by omega
    have : a * (b / a) ≤ a := by nlinarith
    omega
  refine ⟨hq, ?_⟩
  have hbq : (0 : ℚ) < b := by exact_mod_cast (lt_trans ha hab)
  have hqq : (0 : ℚ) < (b / a : ℕ) := by exact_mod_cast (by omega : 0 < b / a)
  have hdq : (a : ℚ) * (b / a : ℕ) = b := by exact_mod_cast hd
  field_simp
  exact hdq

/-- If a reciprocal sum is below `1/z`, every denominator exceeds `z`. -/
theorem denominators_gt_of_sum_lt {k z : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hz : 0 < z)
    (hs : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) < 1 / (z : ℚ)) :
    ∀ i, z < n i := by
  intro i
  have hterm : (1 : ℚ) / (n i : ℚ) ≤ ∑ j : Fin k, 1 / (n j : ℚ) := by
    exact Finset.single_le_sum (f := fun j : Fin k => (1 : ℚ) / (n j : ℚ)) (fun j _ => by positivity) (Finset.mem_univ i)
  have hi : (0 : ℚ) < n i := by exact_mod_cast hn i
  have hzq : (0 : ℚ) < z := by exact_mod_cast hz
  have hlt := lt_of_le_of_lt hterm hs
  have he := (div_lt_div_iff₀ hi hzq).1 hlt
  exact_mod_cast (by simpa using he : (z : ℚ) < n i)

end Problem337

end

end OAI

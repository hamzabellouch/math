import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

def walkWindowLength (n : ℕ) : ℕ := 8 * (n + 1)

def walkWindowLeft (n : ℕ) : ℕ := 2 * (n + 1)

def walkWindowRight (n : ℕ) : ℕ := 6 * (n + 1)

def walkWindowPairs (n : ℕ) : ℕ := 4 * (n + 1)

noncomputable def walkError (n : ℕ) : ℝ := 1 / (10 * (n : ℝ))

@[simp] theorem walkWindowLength_pos (n : ℕ) : 0 < walkWindowLength n := by
  simp [walkWindowLength]

@[simp] theorem walkWindowPairs_pos (n : ℕ) : 0 < walkWindowPairs n := by
  simp [walkWindowPairs]

theorem walkWindowLength_eq_twice_pairs (n : ℕ) :
    walkWindowLength n = 2 * walkWindowPairs n := by
  simp [walkWindowLength, walkWindowPairs]
  omega

theorem walkWindowRight_sub_left (n : ℕ) :
    walkWindowRight n - walkWindowLeft n = walkWindowPairs n := by
  simp [walkWindowRight, walkWindowLeft, walkWindowPairs]
  omega

theorem walkWindowLeft_lt_right (n : ℕ) :
    walkWindowLeft n < walkWindowRight n := by
  simp [walkWindowLeft, walkWindowRight]

theorem walkWindowRight_lt_length (n : ℕ) :
    walkWindowRight n < walkWindowLength n := by
  simp [walkWindowRight, walkWindowLength]

theorem walkError_pos {n : ℕ} (hn : 0 < n) : 0 < walkError n := by
  unfold walkError
  positivity

theorem mul_walkError {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * walkError n = 1 / 10 := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  unfold walkError
  field_simp [hn0]

theorem walk_floor_bounds {n : ℕ} {x : ℝ}
    (hx : |x| < 2 * (n : ℝ)) :
    -(2 * (n : ℤ)) ≤ Int.floor x ∧ Int.floor x ≤ 2 * (n : ℤ) - 1 := by
  rcases abs_lt.mp hx with ⟨hlo, hhi⟩
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact hlo.le
  · have hf : Int.floor x < 2 * (n : ℤ) := by
      apply Int.floor_lt.mpr
      push_cast
      exact hhi
    omega

theorem walk_fractional_bounds {x : ℝ} (hx : ∀ m : ℤ, x ≠ (m : ℝ)) :
    0 < x - (Int.floor x : ℝ) ∧ x - (Int.floor x : ℝ) < 1 := by
  have hf := Int.floor_le x
  have hs := Int.lt_floor_add_one x
  have hne := hx (Int.floor x)
  constructor
  · exact sub_pos.mpr (lt_of_le_of_ne hf (Ne.symm hne))
  · linarith

theorem walk_shift_bounds {n : ℕ} {j m : ℤ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hmlo : -(2 * (n : ℤ)) ≤ m) (hmhi : m ≤ 2 * (n : ℤ) - 1) :
    3 ≤ j - m ∧ j - m ≤ (walkWindowLength n : ℤ) - 2 := by
  simp only [walkWindowLeft, walkWindowRight, walkWindowLength,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  omega

theorem walk_integer_shift_mem_range {n : ℕ} {j : ℤ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ)) :
    -(2 * (n : ℤ)) ≤ j ∧ j ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ) := by
  simp only [walkWindowLeft, walkWindowRight, walkWindowLength,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  omega

theorem walk_translated_shift_mem_range {n : ℕ} {j m : ℤ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hmlo : -(2 * (n : ℤ)) ≤ m) (hmhi : m ≤ 2 * (n : ℤ) - 1) :
    -(2 * (n : ℤ)) ≤ j - m ∧
      j - m ≤ (walkWindowLength n : ℤ) + 2 * (n : ℤ) := by
  obtain ⟨hlo, hhi⟩ := walk_shift_bounds hjlo hjhi hmlo hmhi
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  omega

theorem walk_transport_in_window {n : ℕ} {j : ℤ} {y : ℝ}
    (hjlo : (walkWindowLeft n : ℤ) ≤ j)
    (hjhi : j ≤ (walkWindowRight n : ℤ))
    (hylo : (j : ℝ) - 2 * (n : ℝ) < y)
    (hyhi : y < (j : ℝ) + 1 + 2 * (n : ℝ)) :
    0 < y ∧ y < (walkWindowLength n : ℝ) := by
  have hlo : (walkWindowLeft n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjlo
  have hhi : (j : ℝ) ≤ (walkWindowRight n : ℝ) := by exact_mod_cast hjhi
  simp only [walkWindowLeft, walkWindowRight, walkWindowLength,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
  constructor <;> linarith

end MarkovSuperreflexivity

end OAI

import OAI.Computability.LoopMatching.Accumulator
import OAI.Computability.LoopMatching.CountDecomposition
import OAI.Computability.LoopMatching.ExpandInput
import OAI.Computability.MatchingCount.BinarySolve

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching
open scoped BigOperators

namespace Approximation

def term (G : Input) (j : ℕ) : ℕ :=
  BinaryMatching.Raw.InputData.sparseEstimate (expand G j)

def output (G : Input) : ℕ × ℕ :=
  (Accumulator.Q (term G) G.n, G.n.factorial)

theorem term_bounds (G : Input) (j : ℕ) :
    term G j ≤ BinaryMatching.count (expand G j) ∧
    BinaryMatching.count (expand G j) ≤ 2 ^ (9 * (G.n + j)) * term G j ∧
    (term G j = 0 ↔ BinaryMatching.count (expand G j) = 0) := by
  simpa only [term, expand_n] using
    BinaryMatching.Raw.InputData.sparseEstimate_correct (expand G j)

theorem output_den_pos (G : Input) : 0 < (output G).2 := Nat.factorial_pos _

theorem output_value (G : Input) :
    outputValue (output G) =
      ∑ j ∈ Finset.range (G.n + 1), (term G j : ℚ) / (j.factorial : ℚ) :=
  Accumulator.quotient_eq_sum (term G) G.n

theorem factorial_profile_bounds (a b : ℕ → ℕ) (C n : ℕ)
    (hlo : ∀ j ≤ n, a j ≤ j.factorial * b j)
    (hhi : ∀ j ≤ n, j.factorial * b j ≤ C * a j) :
    Accumulator.Q a n ≤ n.factorial * (∑ j ∈ Finset.range (n + 1), b j) ∧
    n.factorial * (∑ j ∈ Finset.range (n + 1), b j) ≤ C * Accumulator.Q a n := by
  revert hlo hhi
  induction n with
  | zero =>
      intro hlo hhi
      simpa using And.intro (hlo 0 (by omega)) (hhi 0 (by omega))
  | succ n ih =>
      intro hlo hhi
      obtain ⟨hl, hu⟩ := ih (fun j hj => hlo j (by omega))
        (fun j hj => hhi j (by omega))
      have hlastlo := hlo (n + 1) (by omega)
      have hlasthi := hhi (n + 1) (by omega)
      rw [Accumulator.Q_succ, Finset.sum_range_succ]
      constructor
      · calc
          (n + 1) * Accumulator.Q a n + a (n + 1) ≤
              (n + 1) * (n.factorial * (∑ j ∈ Finset.range (n + 1), b j)) +
                (n + 1).factorial * b (n + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hl) hlastlo
          _ = (n + 1).factorial *
              ((∑ j ∈ Finset.range (n + 1), b j) + b (n + 1)) := by
            rw [Nat.factorial_succ]; ring
      · calc
          (n + 1).factorial *
              ((∑ j ∈ Finset.range (n + 1), b j) + b (n + 1)) =
              (n + 1) * (n.factorial * (∑ j ∈ Finset.range (n + 1), b j)) +
                (n + 1).factorial * b (n + 1) := by
            rw [Nat.factorial_succ]; ring
          _ ≤ (n + 1) * (C * Accumulator.Q a n) + C * a (n + 1) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hu) hlasthi
          _ = C * ((n + 1) * Accumulator.Q a n + a (n + 1)) := by ring

theorem output_bounds_of_expanded_count (G : Input)
    (expanded_count : ∀ j ≤ G.n,
      BinaryMatching.count (expand G j) = j.factorial * countWithLoops G j) :
    (output G).1 ≤ (output G).2 * count G ∧
    (output G).2 * count G ≤ 2 ^ (18 * G.n) * (output G).1 ∧
    ((output G).1 = 0 ↔ count G = 0) := by
  have hlo : ∀ j ≤ G.n, term G j ≤ j.factorial * countWithLoops G j := by
    intro j hj
    rw [← expanded_count j hj]
    exact (term_bounds G j).1
  have hhi : ∀ j ≤ G.n,
      j.factorial * countWithLoops G j ≤ 2 ^ (18 * G.n) * term G j := by
    intro j hj
    rw [← expanded_count j hj]
    apply (term_bounds G j).2.1.trans
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ))
    omega
  obtain ⟨hl, hu⟩ := factorial_profile_bounds (term G) (countWithLoops G)
    (2 ^ (18 * G.n)) G.n hlo hhi
  rw [← count_eq_sum_countWithLoops G] at hl hu
  change (output G).1 ≤ (output G).2 * count G at hl
  change (output G).2 * count G ≤ 2 ^ (18 * G.n) * (output G).1 at hu
  refine ⟨hl, hu, ?_⟩
  constructor
  · intro hz
    rw [hz, mul_zero] at hu
    have hprod : (output G).2 * count G = 0 := Nat.eq_zero_of_le_zero hu
    exact (Nat.mul_eq_zero.mp hprod).resolve_left (Nat.ne_of_gt (output_den_pos G))
  · intro hz
    rw [hz, mul_zero] at hl
    exact Nat.eq_zero_of_le_zero hl

theorem output_magnitude (G : Input) (B : ℕ)
    (hB : ∀ j ≤ G.n, term G j ≤ B) :
    (output G).1 ≤ (G.n + 1).factorial * B ∧
    (output G).2 = G.n.factorial :=
  ⟨Accumulator.Q_le_factorial_mul (term G) G.n B hB, rfl⟩

private theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ n := by positivity
      omega

theorem factorial_le_two_pow_square (n : ℕ) : n.factorial ≤ 2 ^ (n * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
        _ ≤ 2 ^ n * 2 ^ (n * n) := Nat.mul_le_mul (succ_le_two_pow n) ih
        _ = 2 ^ (n + n * n) := (pow_add 2 n (n * n)).symm
        _ ≤ 2 ^ ((n + 1) * (n + 1)) := by
          apply Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ))
          nlinarith

theorem output_exponential_magnitude (G : Input) (B : ℕ)
    (hB : ∀ j ≤ G.n, term G j ≤ 2 ^ B) :
    (output G).1 ≤ 2 ^ ((G.n + 1) * (G.n + 1) + B) ∧
    (output G).2 ≤ 2 ^ (G.n * G.n) := by
  constructor
  · calc
      (output G).1 ≤ (G.n + 1).factorial * 2 ^ B :=
        (output_magnitude G (2 ^ B) hB).1
      _ ≤ 2 ^ ((G.n + 1) * (G.n + 1)) * 2 ^ B :=
        Nat.mul_le_mul_right _ (factorial_le_two_pow_square (G.n + 1))
      _ = 2 ^ ((G.n + 1) * (G.n + 1) + B) := (pow_add _ _ _).symm
  · exact factorial_le_two_pow_square G.n

end Approximation
end LoopMatching

end OAI

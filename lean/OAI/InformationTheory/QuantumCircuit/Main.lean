import OAI.InformationTheory.QuantumCircuit.Parity

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- Measured-output parity for a polynomial qubit bound with a fixed multiplicative constant. -/
theorem parity_lower_bound_polynomial_size (d k C : ℕ)
    (_hd : 0 < d) (_hk : 0 < k) (_hC : 0 < C) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → N ≤ C * (n + 1) ^ k →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ∃ x : Word n,
          successProbability (physicalCircuitMatrix layers) out x < (2 : ℝ) / 3 := by
  classical
  obtain ⟨n₀, h₀⟩ := parity_lower_bound d ((k + 1 : ℕ) : ℝ) (1 / 6)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) (by norm_num) (by norm_num)
  refine ⟨max n₀ (max 1 (C * 2 ^ k)), ?_⟩
  intro n hn N hnN hN layers hdepth out
  rcases max_le_iff.mp hn with ⟨hn₀, hnrest⟩
  rcases max_le_iff.mp hnrest with ⟨hn1, hCn⟩
  have hpoly : N ≤ n ^ (k + 1) := by
    calc
      N ≤ C * (n + 1) ^ k := hN
      _ ≤ C * (2 * n) ^ k :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) k)
      _ = (C * 2 ^ k) * n ^ k := by rw [mul_pow, Nat.mul_assoc]
      _ ≤ n * n ^ k := Nat.mul_le_mul_right (n ^ k) hCn
      _ = n ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  have hsize : (N : ℝ) ≤ (n : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hpoly
  have hnot := h₀ n hn₀ N hnN hsize layers hdepth out
  push Not at hnot
  norm_num at hnot
  exact hnot

end QAC

end

end OAI

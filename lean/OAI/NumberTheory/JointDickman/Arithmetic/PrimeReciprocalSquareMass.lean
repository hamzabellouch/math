import OAI.NumberTheory.JointDickman.Amplification.ChebyshevDischarge

namespace OAI

/-! # Reciprocal-square mass of a dyadic prime interval -/
namespace JointDickman
open Finset

/-- Chebyshev's proved prime bound supplies the second logarithmic saving
when sparse sampling is applied to a reciprocal prime polynomial. -/
theorem prime_reciprocal_square_mass : ∃ D : ℝ, 0 < D ∧
    ∀ (N : ℝ), 2 ≤ N → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∑ p ∈ Q, 1/(p:ℝ)^2) ≤ D/(N*Real.log N) := by
  obtain ⟨C,hC,hcount⟩ := chebyshevPrimeCountingInput
  refine ⟨2*(C+1),by positivity,?_⟩
  intro N hN Q hQ
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2 : Real.log N ≤ Real.log (2*N) :=
    Real.log_le_log hN0 (by linarith)
  have hcard : (Q.card:ℝ) ≤ C*(2*N)/Real.log (2*N) := by
    apply le_trans (b := (Nat.primeCounting ⌊2*N⌋₊:ℝ))
    · rw [← Nat.primesLE_card_eq_primeCounting]
      exact_mod_cast card_le_card (show Q ⊆ Nat.primesLE ⌊2*N⌋₊ by
        intro p hp
        exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hQ p hp).2.2, (hQ p hp).1⟩)
    · exact hcount (2*N) (by linarith)
  have hcard' : (Q.card:ℝ) ≤ 2*C*N/Real.log N := by
    exact hcard.trans (by
      rw [show C*(2*N)=2*C*N by ring]
      exact div_le_div_of_nonneg_left (by positivity) hlog hlog2)
  calc
    _ ≤ ∑ _p ∈ Q, 1/N^2 := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (sq_pos_of_pos hN0)
        (pow_le_pow_left₀ hN0.le (hQ p hp).2.1 2)
    _ = (Q.card:ℝ)/N^2 := by simp [div_eq_mul_inv]
    _ ≤ (2*C*N/Real.log N)/N^2 := div_le_div_of_nonneg_right hcard' (sq_nonneg N)
    _ = 2*C/(N*Real.log N) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end JointDickman

end OAI

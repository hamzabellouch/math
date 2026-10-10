import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GridGroundUpper
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.RoundingPolynomialBudget

namespace OAI

/-! Explicit polynomial precision for the emitted nodes: separation and the
full-ground rounding budget account for all nuclei in the centered box. -/

noncomputable section
open scoped NNReal
namespace ContinuumCoulomb

theorem exists_grid_node_separation_offset (J : ℝ≥0) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ k a : ℕ, q+10*k ≤ a →
    ∀ (N : ℝ) (P : ℕ), 2 ≤ N → N^a ≤ (P:ℝ) →
      2*(J:ℝ)*((P:ℝ)+1)⁻¹ < (1/(N^k)^10)/3 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds
    (by norm_num : (0:ℝ)<1) (6*(J:ℝ))
  refine ⟨q,by omega,fun k a ha N P hN hP => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hmul : 6*(J:ℝ)*(N^k)^10 < (P:ℝ)+1 := by
    calc
      _ ≤ N^q*(N^k)^10 := mul_le_mul_of_nonneg_right (hbound N hN).2 (by positivity)
      _ = N^(q+10*k) := by rw [pow_add,← pow_mul]; congr 2; omega
      _ ≤ N^a := pow_le_pow_right₀ hN1 ha
      _ < _ := by linarith only [hP]
  rw [← div_eq_mul_inv,div_div]
  apply (div_lt_div_iff₀ (by positivity) (by positivity : 0 < (N^k)^10*3)).mpr
  nlinarith only [hmul]

theorem grid_node_rounding_budget {N scale Q M E : ℝ} (hN : 2 ≤ N) (hs : 1 ≤ scale)
    {q r v p k a P : ℕ} (ha : q+465*k+2*r+v+p+32 ≤ a) (hP : N^a ≤ (P:ℝ))
    (hQ : 0 ≤ Q) (hQN : Q ≤ N^(135*k+8)) (hM : 0 ≤ M) (hMN : M ≤ N^r)
    (hE : E ≤ N^(q+60*k+r+v)) :
    32*(scale⁻¹*((P:ℝ)+1)⁻¹)*Q ≤ 1 ∧
      32*(scale⁻¹*((P:ℝ)+1)⁻¹)*Q*(E+4*M*Q^2) ≤ (N^p)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hs0 : 0 < scale := lt_of_lt_of_le zero_lt_one hs
  apply rounding_polynomial_budget hN (a := a) (c := q+60*k+r+v)
    (q := 135*k+8) (r := r) (p := p) (by omega) hQ hQN hM hMN hE (by positivity)
  calc
    _ ≤ 1*((P:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hs) (by positivity)
    _ ≤ (N^a)⁻¹ := by
      rw [one_mul]
      exact inv_anti₀ (pow_pos hN0 a) (by linarith only [hP])

end ContinuumCoulomb

end

end OAI

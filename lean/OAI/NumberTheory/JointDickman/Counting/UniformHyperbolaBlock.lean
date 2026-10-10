import OAI.NumberTheory.JointDickman.Amplification.HyperbolaBudget

namespace OAI

/-! # Uniform normalization of the prime hyperbola block estimate -/
namespace JointDickman
open Finset

noncomputable def rationalHyperbolaBudget (N Z L : ℝ) (q : ℕ) : ℝ :=
  2*L/Z+4*(1+Real.log q)/q+4/Z+2*q*(1+L)/N

theorem uniform_prime_hyperbola_block_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (M : ℕ → ℕ) (b c : ℕ → ℂ) (z U H Q q a : ℕ)
      (N Z L : ℝ),
    0 < H → 2 ≤ Q → 0 < q → a.Coprime q → 0 < N → 0 < Z → 0 ≤ L →
    Real.log Q ≤ L → (Q:ℝ)*U ≤ 2*N → (U:ℝ) ≤ N/Z → (Q:ℝ) ≤ 2*N/Z →
    (∀ p ∈ P, p.Prime ∧ p ≤ Q) → (∀ p ∈ P, z ≤ M p ∧ M p ≤ U) →
    (∀ p ∈ P, ‖b p‖ ≤ Real.log p) → (∀ m, ‖c m‖ ≤ 1) →
    ‖∑ p ∈ P, ∑ m ∈ Ioc z (M p), b p*c m*additivePhase ((a:ℝ)/q*p*m)‖ ≤
      N*(Real.log 4*(2/(H:ℝ)+2/Z) + H*Real.sqrt (C*rationalHyperbolaBudget N Z L q)) := by
  obtain ⟨C,hC,hblock⟩ := prime_hyperbola_block_bound
  refine ⟨C,hC,?_⟩
  intro P M b c z U H Q q a N Z L hH hQ hq ha hN hZ hL hlog hQU hU hQZ hP hM hb hc
  have h := hblock P M b c z U H Q q a hH hQ hq ha hP hM hb hc
  have hbudget := rectangle_budget_uniform Q U q N Z L hN hZ hq hL hlog hQU hU hQZ
  have hsqrt : Real.sqrt (C*((Q:ℝ)*Real.log Q*(U:ℝ)^2 +
      Q*(U:ℝ)^2*Q*(1+Real.log q)/q + Q*U*Q + Q*U*q*(1+Real.log Q))) ≤
      N*Real.sqrt (C*rationalHyperbolaBudget N Z L q) := by
    have hmul := mul_le_mul_of_nonneg_left hbudget hC.le
    have he : C*(N^2*(2*L/Z+4*(1+Real.log q)/q+4/Z+2*q*(1+L)/N)) =
        N^2*(C*rationalHyperbolaBudget N Z L q) := by
      unfold rationalHyperbolaBudget
      ring
    rw [he] at hmul
    apply (Real.sqrt_le_sqrt hmul).trans_eq
    rw [Real.sqrt_mul (sq_nonneg N),Real.sqrt_sq hN.le]
  apply h.trans
  have hround := rounding_budget_uniform U H Q N Z hH hN.le hZ hQU hQZ
  have htotal := add_le_add hround (mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg H))
  convert htotal using 1
  ring

end JointDickman

end OAI

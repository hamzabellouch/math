import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallDivisorEnergy

namespace OAI

/-! # The fixed off-witness family has exponentially small coefficient norm -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- This is a conditional estimate for the explicitly defined subfamily
where each small-kernel value is below the witness threshold. The pointwise
condition is part of the subfamily, not an additional published input. -/
theorem eventual_off_witness_norm (C₀ ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (M : ℕ) (S : Finset ℕ) (u : ℝ),
      (M : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) → 0 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (c : Finset ℕ → ℂ) (G : Finset ℕ → ℕ → ℂ),
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ s ∈ S, ∀ U ∈ P.powerset,
        ‖G U s‖ ≤ Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ) / 10) * (Real.sqrt 2) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
        Real.exp ((-4 / 5 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [squarefree_coefficient_budget C₀ (2 * ε) (by positivity)] with T hb
  intro P M S u hM hcard hS hu huU c G hc hG
  let K := T ^ (9999999 / 10000000 : ℝ)
  have hpoly : (1 + Real.sqrt 2 / 16) ^ P.card ≤ Real.exp (K / 10) :=
    (small_kernel_divisor_product_bound P.card).trans (Real.exp_le_exp.mpr (by linarith))
  have hpoint (s : ℕ) (hs : s ∈ S) :
      ‖∑ U ∈ P.powerset, c U * G U s‖ ≤ Real.exp (-4 * K / 5) := by
    apply (small_divisor_combination_bound P c (fun U => G U s)
      (Real.exp (-9 * K / 10)) (Real.exp_nonneg _) hc (hG s hs)).trans
    apply (mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤ Real.exp (ε * K) := by
    apply (Real.sqrt_le_sqrt (hb M S u hM hS hu huU)).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  apply (sqrt_weighted_energy_le_uniform S (fun s => u ^ s.primeFactors.card / (s : ℝ)) _
    (Real.exp (-4 * K / 5)) (Real.exp_nonneg _) (fun _ _ => by positivity) hpoint).trans
  apply (mul_le_mul_of_nonneg_left hsqrt (Real.exp_nonneg _)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end Ostmann

end OAI

import OAI.NumberTheory.JointDickman.Probability.ResidueFourierParseval

namespace OAI

/-! # The local histogram Fourier bound in finite-cell form -/

namespace JointDickman
open Finset

/-- The local window length is card(J)*delta. It is retained explicitly,
so summing boxes can use bounded overlap rather than their number. -/
theorem finite_histogram_fourier_bound {ι : Type*} [DecidableEq ι]
    {q : ℕ} [NeZero q] (J : Finset ι) {δ M : ℝ}
    (_hδ : 0 ≤ δ) (_hM : 0 ≤ M) (U : ι → (ZMod q)ˣ → ℝ)
    (v : (ZMod q)ˣ → ℂ)
    (hv : ∀ r, ‖v r‖ ≤ δ*M*(∑ i ∈ J, U i r)) :
    (∑ h : ZMod q, ‖unitResidueFourier v h/(q.totient : ℂ)‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*δ)*M^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (δ/(q.totient : ℝ))*U i r^2) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hper (r : (ZMod q)ˣ) : ‖v r‖^2 ≤
      δ^2*M^2*(J.card : ℝ)*(∑ i ∈ J, U i r^2) := by
    have hupper : 0 ≤ δ*M*(∑ i ∈ J, U i r) := (norm_nonneg _).trans (hv r)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hupper).mpr (hv r)
    have hc : (∑ i ∈ J, U i r)^2 ≤ (J.card : ℝ)*(∑ i ∈ J, U i r^2) := by
      simpa using sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) (fun i => U i r)
    calc
      ‖v r‖^2 ≤ (δ*M)^2*(∑ i ∈ J, U i r)^2 := by simpa only [mul_pow] using hsq
      _ ≤ (δ*M)^2*((J.card : ℝ)*(∑ i ∈ J, U i r^2)) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = _ := by ring
  rw [normalizedUnitResidue_fourier_parseval]
  calc
    _ ≤ ((q : ℝ)/(q.totient : ℝ))*((1/(q.totient : ℝ))*
        ∑ r : (ZMod q)ˣ, δ^2*M^2*(J.card : ℝ)*(∑ i ∈ J, U i r^2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hper r)) (by positivity))
        (by positivity)
    _ = _ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro r _
      ring

end JointDickman

end OAI

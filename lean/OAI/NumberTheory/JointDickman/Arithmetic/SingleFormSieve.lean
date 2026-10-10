import OAI.NumberTheory.JointDickman.Arithmetic.SieveInterval
import OAI.NumberTheory.JointDickman.Counting.TiltedCoefficientTriple

namespace OAI

/-! # The single-form sieve, with the same actual tilted weights -/

namespace JointDickman

open Finset

theorem single_form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ) (u v Z : ℕ),
      u ≤ v → 2 ≤ Z → (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 ≤ p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico u v, ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p)) ≤
        C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) + 2 * (Z + 1 : ℝ) * Z := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve_polynomial hFord hM (by norm_num : 0 < (1 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ u v Z huv hZ hP hθ
  have hb := hbound P (fun _ => {0}) θ u v Z huv hZ
    (fun p hp => by simpa using hP p hp) (fun _ _ => by simp) hθ
  have heq (n : ℕ) : (∏ p ∈ rootEvents P (fun _ => {0}) n, θ p) =
      ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) := by
    simp only [rootEvents, prod_filter, mem_singleton, residueWeight]
    congr!
  simp_rw [heq] at hb
  have hfactor (p : ℕ) : 1 - 1 / (p : ℝ) + 1 / p * θ p = 1 - (1 - θ p) / p := by ring
  simpa only [card_singleton, Nat.cast_one, pow_one, hfactor] using hb

end JointDickman

end OAI

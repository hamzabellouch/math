import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergy

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def quadraticLowWeightIndices (S L : ℕ) (u K : ℝ) : Finset ℕ :=
  (Finset.Ico S (2*S)).filter (fun s =>
    Squarefree s ∧ s.Coprime L ∧ u ^ s.primeFactors.card ≤ Real.exp (K / 200))

theorem divisorQuadraticCombination_restricted_energy_le {L S v : ℕ}
    (hL : Squarefree L) (hS : L ^ 2 ≤ S) (hv : 0 < v)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : ℕ → ℂ) (hη : ∀ d ∈ L.divisors, ‖η d‖ ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ)
    (T : Finset ℕ) (hT : T ⊆ Finset.Ico S (2*S)) (weight : ℕ → ℝ)
    (W : ℝ) (hW : 0 ≤ W) (hweight : ∀ s ∈ T, weight s ≤ W) :
    (∑ s ∈ T, (weight s / s) *
      ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2) ≤
      W * (quadraticCorrelationConstant *
        ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ))) := by
  let E : ℕ → ℝ := fun s => (s : ℝ)⁻¹ *
    ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2
  have hE (s : ℕ) : 0 ≤ E s := by dsimp [E]; positivity
  calc
    _ = ∑ s ∈ T, weight s * E s := by
      apply Finset.sum_congr rfl
      intro s hs
      dsimp [E]
      ring
    _ ≤ ∑ s ∈ T, W * E s :=
      Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_right (hweight s hs) (hE s))
    _ = W * ∑ s ∈ T, E s := (Finset.mul_sum T E W).symm
    _ ≤ W * ∑ s ∈ Finset.Ico S (2*S), E s :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hT (fun s hs hnot => hE s)) hW
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (divisorQuadraticCombination_energy_le hL hS hv lam hlam η hη A mInv hR h θ) hW

theorem divisorQuadraticCombination_lowWeight_energy_le {L S v : ℕ}
    (hL : Squarefree L) (hS : L ^ 4 ≤ S) (hv : 0 < v)
    (lam : ℝ) (hlam : 0 ≤ lam) (η : ℕ → ℂ) (hη : ∀ d ∈ L.divisors, ‖η d‖ ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R : ℝ} (hR : 0 < R) (h θ u K : ℝ) :
    (∑ s ∈ quadraticLowWeightIndices S L u K, (u ^ s.primeFactors.card / s) *
      ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2) ≤
      Real.exp (K / 200) * (quadraticCorrelationConstant *
        ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ))) := by
  have hS' : L ^ 2 ≤ S :=
    (pow_le_pow_right₀ (Nat.pos_of_ne_zero hL.ne_zero : 1 ≤ L) (by decide : 2 ≤ 4)).trans hS
  apply divisorQuadraticCombination_restricted_energy_le hL hS' hv lam hlam η hη A mInv hR h θ
    (quadraticLowWeightIndices S L u K) (Finset.filter_subset _ _)
    (fun s => u ^ s.primeFactors.card) (Real.exp (K / 200)) (Real.exp_pos _).le
  intro s hs
  exact (Finset.mem_filter.mp hs).2.2.2

end Ostmann.QuadraticCenter

end

end OAI

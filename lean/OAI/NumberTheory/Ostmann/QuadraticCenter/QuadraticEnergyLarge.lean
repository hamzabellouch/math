import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyHighWeight
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyLowWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem quadratic_energy_low_high_partition {A : Type*} [AddCommMonoid A]
    (S L : ℕ) (u K : ℝ) (F : ℕ → A) :
    (∑ s ∈ (Finset.Ico S (2*S)).filter (fun s => Squarefree s ∧ s.Coprime L), F s) =
      (∑ s ∈ quadraticLowWeightIndices S L u K, F s) +
      ∑ s ∈ quadraticHighWeightIndices S L u K, F s := by
  simp only [quadraticLowWeightIndices, quadraticHighWeightIndices, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsc : Squarefree s ∧ s.Coprime L
  · by_cases hw : u ^ s.primeFactors.card ≤ Real.exp (K/200)
    · rw [ite_eq_left hsc, ite_eq_left ⟨hsc.1, hsc.2, hw⟩,
        ite_eq_right (fun h => (not_lt_of_ge hw) h.2.2), add_zero]
    · rw [ite_eq_left hsc, ite_eq_right (fun h => hw h.2.2),
        ite_eq_left ⟨hsc.1, hsc.2, lt_of_not_ge hw⟩, zero_add]
  · rw [ite_eq_right hsc, ite_eq_right (fun h => hsc ⟨h.1, h.2.1⟩),
      ite_eq_right (fun h => hsc ⟨h.1, h.2.1⟩), add_zero]

theorem divisorQuadraticCombination_large_energy_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L S v : ℕ), Squarefree L → 2 ≤ L → L ^ 4 ≤ S → 0 < v →
      ∀ (u K : ℝ), (S : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      ∀ (lam : ℝ), 0 ≤ lam → ∀ (η : ℕ → ℂ), (∀ d ∈ L.divisors, ‖η d‖ ≤ 1) →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Ico S (2*S)).filter (fun s => Squarefree s ∧ s.Coprime L),
        (u ^ s.primeFactors.card / s) *
          ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2) ≤
        Real.exp (K/200) * (quadraticCorrelationConstant *
          ∏ p ∈ L.primeFactors, (1 + lam ^ 2 + 2 * lam / Real.sqrt (p : ℝ))) +
        cutoffFourierBound ^ 2 * Real.exp (-10*K) * (1+lam) ^ (2 * L.primeFactors.card) := by
  filter_upwards [divisorQuadraticCombination_highWeight_energy_eventually] with T hT
  intro L S v hL hL2 hS hv u K hSupper hu huupper hK lam hlam η hη A mInv R h θ hR
  have hLsq : 2 ≤ L ^ 2 := by nlinarith
  have hS' : 2 * L ^ 2 ≤ S := by
    calc
      _ ≤ L ^ 2 * L ^ 2 := Nat.mul_le_mul_right _ hLsq
      _ = L ^ 4 := by ring
      _ ≤ S := hS
  rw [quadratic_energy_low_high_partition S L u K]
  exact add_le_add
    (divisorQuadraticCombination_lowWeight_energy_le hL hS hv lam hlam η hη A mInv hR h θ u K)
    (hT L S v hL hS' hv u K hSupper hu huupper hK lam hlam η hη A mInv R h θ hR)

end Ostmann.QuadraticCenter

end

end OAI

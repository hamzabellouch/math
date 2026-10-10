import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyHighDivisors
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyWeighted

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology ComplexConjugate
open Filter

theorem divisorQuadraticCombination_highWeight_energy_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (L S v : ℕ), Squarefree L → 2 * L ^ 2 ≤ S → 0 < v →
      ∀ (u K : ℝ), (S : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      ∀ (lam : ℝ), 0 ≤ lam → ∀ (η : ℕ → ℂ), (∀ d ∈ L.divisors, ‖η d‖ ≤ 1) →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ quadraticHighWeightIndices S L u K, (u ^ s.primeFactors.card / s) *
        ‖divisorQuadraticCombination L lam η A mInv s v R h θ‖ ^ 2) ≤
        cutoffFourierBound ^ 2 * Real.exp (-10 * K) * (1 + lam) ^ (2 * L.primeFactors.card) := by
  filter_upwards [divisorQuadraticSum_high_correlation_eventually] with T hT
  intro L S v hL hS hv u K hSupper hu huupper hK lam hlam η hη A mInv R h θ hR
  have hu0 : 0 ≤ u := (by linarith : 0 < u).le
  let a : ℕ → ℂ := fun d => (lam : ℂ) ^ d.primeFactors.card * η d
  let G : ℕ → ℕ → ℂ := fun d s => divisorQuadraticSum d A (mInv d) s v R h θ
  let B : ℝ := cutoffFourierBound ^ 2 * Real.exp (-10*K)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha (d : ℕ) (hd : d ∈ L.divisors) : ‖a d‖ ≤ lam ^ d.primeFactors.card := by
    dsimp [a]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hη d hd) (pow_nonneg hlam _)
  calc
    _ ≤ ∑ d ∈ L.divisors, ∑ e ∈ L.divisors, ‖a d‖ * ‖a e‖ *
        ‖∑ s ∈ quadraticHighWeightIndices S L u K, ((u ^ s.primeFactors.card : ℝ) : ℂ) *
          (G d s * conj (G e s) / (s : ℂ))‖ :=
      weighted_complex_energy_le_correlations_general L.divisors
        (quadraticHighWeightIndices S L u K) (fun s => u ^ s.primeFactors.card)
        (fun s hs => pow_nonneg hu0 _) a G
    _ ≤ ∑ d ∈ L.divisors, ∑ e ∈ L.divisors,
        lam ^ d.primeFactors.card * lam ^ e.primeFactors.card * B := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul
      · exact mul_le_mul (ha d hd) (ha e he) (norm_nonneg _) (pow_nonneg hlam _)
      · exact hT L S d e hL (Nat.dvd_of_mem_divisors hd) (Nat.dvd_of_mem_divisors he)
          u K hS hSupper hu huupper hK A (mInv d) (mInv e) v hv R h θ hR
      · exact norm_nonneg _
      · exact mul_nonneg (pow_nonneg hlam _) (pow_nonneg hlam _)
    _ = B * (∑ d ∈ L.divisors, lam ^ d.primeFactors.card) ^ 2 := by
      rw [pow_two]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = _ := by
      rw [squarefree_divisor_weight_sum hL, ← pow_mul]
      simp only [B, Nat.mul_comm]

end Ostmann.QuadraticCenter

end

end OAI

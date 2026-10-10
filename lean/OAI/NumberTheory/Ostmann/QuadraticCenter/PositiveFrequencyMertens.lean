import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightEndpoint
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyEnvelopeEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyEuler

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positiveArrayEnvelope_one_sq (L : ℕ) (lam : ℝ) :
    (positiveArrayEnvelope L lam 1)^2 =
      (L : ℝ)*cutoffFourierBound^2*(1+lam)^(2*L.primeFactors.card)*(reciprocalSqrtDivisorSum L)^2 := by
  simp only [positiveArrayEnvelope, Nat.cast_one, div_one, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg L), ← pow_mul, reciprocalSqrtDivisorSum]
  rw [Nat.mul_comm L.primeFactors.card 2]

theorem positiveDivisorArray_nontrivial_energy_mertens :
    ∃ C : ℝ, 0 < C ∧ ∀ (L q P Z B : ℕ), Squarefree L → q ≠ 0 → P ∣ q → P ≠ 1 →
      0 < Z → 1 ≤ B → (∀ p ∈ q.primeFactors, Z ≤ p) →
      ∀ (lam u : ℝ), 0 ≤ lam → 0 ≤ u →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
        u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv P R h θ s‖^2) ≤
      (positiveArrayEnvelope L lam 1/(Z : ℝ))^2 *
        Real.exp (u*(Real.log (Real.log (2*(B : ℝ)))+C)) := by
  obtain ⟨C, hC, hM⟩ := highWeightPrimeCutoff_reciprocal_upper
  refine ⟨C, hC, ?_⟩
  intro L q P Z B hL hq hP hPone hZ hB hprimes lam u hlam hu A mInv R h θ hR
  let S := (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L)
  have hS : ∀ s ∈ S, Squarefree s := fun s hs => (Finset.mem_filter.mp hs).2.1
  have hcover : ∀ s ∈ S, s.primeFactors ⊆ highWeightPrimeCutoff B := by
    intro s hs p hp
    have hsp := (Nat.mem_primeFactors.mp hp)
    have hsB := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hsp.1.pos, ?_⟩, hsp.1⟩
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hsp.2.2) hsp.2.1).trans (by omega)
  apply (positiveDivisorArray_nontrivial_weighted_energy hL hq hP hPone hZ hprimes hlam hu
    A mInv hR h θ S (highWeightPrimeCutoff B) (highWeightPrimeCutoff_prime B) hS hcover).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (Real.prod_one_add_le_exp_sum (highWeightPrimeCutoff B)
    (f := fun p : ℕ => u/(p : ℝ)) (fun p => by positivity)).trans
  apply Real.exp_le_exp.mpr
  calc
    _ = u*∑ p ∈ highWeightPrimeCutoff B, 1/(p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM B hB) hu

end Ostmann.QuadraticCenter

end

end OAI

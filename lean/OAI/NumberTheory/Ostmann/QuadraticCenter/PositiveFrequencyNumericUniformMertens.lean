import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyMertens

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positiveDivisorArray_uniform_weighted_energy {L P Z : ℕ}
    (hL : Squarefree L) (q : ℕ) (hP : Z ≤ P) (hZ : 0 < Z)
    {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ) (S V : Finset ℕ)
    (hV : ∀ p ∈ V, Nat.Prime p) (hS : ∀ s ∈ S, Squarefree s)
    (hcover : ∀ s ∈ S, s.primeFactors ⊆ V) :
    (∑ s ∈ S, u^s.primeFactors.card *
      ‖positiveDivisorArray L q lam A mInv P R h θ s‖^2) ≤
      (positiveArrayEnvelope L lam 1 / (Z : ℝ))^2 * ∏ p ∈ V, (1+u/(p : ℝ)) := by
  apply (positiveDivisorArray_weighted_energy_le_euler hL q hlam hu A mInv P hR h θ S V
    hV hS hcover).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p hp => by positivity))
  apply pow_le_pow_left₀ (positiveArrayEnvelope_nonneg L P hlam)
  rw [positiveArrayEnvelope_eq_one_div]
  exact div_le_div_of_nonneg_left (positiveArrayEnvelope_nonneg L 1 hlam)
    (by exact_mod_cast hZ) (by exact_mod_cast hP)

theorem positiveDivisorArray_uniform_energy_mertens :
    ∃ C : ℝ, 0 < C ∧ ∀ (L q P Z B : ℕ), Squarefree L → Z ≤ P →
      0 < Z → 1 ≤ B →
      ∀ (lam u : ℝ), 0 ≤ lam → 0 ≤ u →
      ∀ (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (R h θ : ℝ), 0 < R →
      (∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
        u^s.primeFactors.card * ‖positiveDivisorArray L q lam A mInv P R h θ s‖^2) ≤
      (positiveArrayEnvelope L lam 1/(Z : ℝ))^2 *
        Real.exp (u*(Real.log (Real.log (2*(B : ℝ)))+C)) := by
  obtain ⟨C, hC, hM⟩ := highWeightPrimeCutoff_reciprocal_upper
  refine ⟨C, hC, ?_⟩
  intro L q P Z B hL hP hZ hB lam u hlam hu A mInv R h θ hR
  let S := (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L)
  have hS : ∀ s ∈ S, Squarefree s := fun s hs => (Finset.mem_filter.mp hs).2.1
  have hcover : ∀ s ∈ S, s.primeFactors ⊆ highWeightPrimeCutoff B := by
    intro s hs p hp
    have hsp := (Nat.mem_primeFactors.mp hp)
    have hsB := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hsp.1.pos, ?_⟩, hsp.1⟩
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hsp.2.2) hsp.2.1).trans (by omega)
  apply (positiveDivisorArray_uniform_weighted_energy hL q hP hZ hlam hu
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

import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyEnvelope

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positiveDivisorArray_weighted_energy_le_euler {L : ℕ} (hL : Squarefree L)
    (q : ℕ) {lam u : ℝ} (hlam : 0 ≤ lam) (hu : 0 ≤ u)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℕ → ℤ) (P : ℕ)
    {R : ℝ} (hR : 0 < R) (h θ : ℝ) (S V : Finset ℕ)
    (hV : ∀ p ∈ V, Nat.Prime p) (hS : ∀ s ∈ S, Squarefree s)
    (hcover : ∀ s ∈ S, s.primeFactors ⊆ V) :
    (∑ s ∈ S, u^s.primeFactors.card *
      ‖positiveDivisorArray L q lam A mInv P R h θ s‖^2) ≤
      (positiveArrayEnvelope L lam P)^2 * ∏ p ∈ V, (1+u/(p : ℝ)) := by
  calc
    _ ≤ ∑ s ∈ S, u^s.primeFactors.card *
        ((positiveArrayEnvelope L lam P)^2 / (s : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hu _)
      have hh := positiveDivisorArray_norm_envelope hL q hlam A mInv
        (Nat.pos_of_ne_zero (hS s hs).ne_zero) P hR h θ
      have hh2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg s)] using hh2
    _ = (positiveArrayEnvelope L lam P)^2 *
        (∑ s ∈ S, u^s.primeFactors.card / (s : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (squarefree_weight_sum_le_euler_product V S hV hS hcover hu) (sq_nonneg _)

theorem nontrivial_divisor_ge_prime_lower {q P Z : ℕ} (hq : q ≠ 0)
    (hP : P ∣ q) (hPone : P ≠ 1)
    (hprimes : ∀ p ∈ q.primeFactors, Z ≤ p) : Z ≤ P := by
  obtain ⟨p, hp, hpP⟩ := Nat.exists_prime_and_dvd hPone
  exact (hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hpP.trans hP, hq⟩)).trans
    (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hP (Nat.pos_of_ne_zero hq)) hpP)

theorem positiveArrayEnvelope_eq_one_div (L P : ℕ) (lam : ℝ) :
    positiveArrayEnvelope L lam P = positiveArrayEnvelope L lam 1 / P := by
  unfold positiveArrayEnvelope
  norm_num
  ring

theorem positiveDivisorArray_nontrivial_weighted_energy {L q P Z : ℕ}
    (hL : Squarefree L) (hq : q ≠ 0) (hP : P ∣ q) (hPone : P ≠ 1)
    (hZ : 0 < Z) (hprimes : ∀ p ∈ q.primeFactors, Z ≤ p)
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
    (by exact_mod_cast hZ) (by exact_mod_cast nontrivial_divisor_ge_prime_lower hq hP hPone hprimes)

end Ostmann.QuadraticCenter

end

end OAI

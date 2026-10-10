import OAI.NumberTheory.CubicMoment.Estimates.WeightedSquarefreeMean
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeThirdMoment
import OAI.NumberTheory.CubicMoment.Estimates.DivisorRowEnergy

namespace OAI

/-! Summing actual coprimality rows adds one divisor factor to the norm-fiber
weight. The resulting third divisor moment is logarithmic. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma weighted_divisor_row_energy (S U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hU : ∀ p ∈ U, primaryPrime p) (hS : ∀ b ∈ S, primary b) :
    (∑ s ∈ U.powerset, ∑ b ∈ S.filter (fun b => (∏ p ∈ s, p) ∣ b),
      (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) ≤
        ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hc : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors b).card := by
    exact_mod_cast prime_subset_divisor_count U hU (hS b hb)
  calc
    _ ≤ (2:ℝ)^(primaryPrimeFactors b).card*((4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [←mul_assoc,←mul_pow]; norm_num

lemma ordinary_divisor_row_energy (S U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hU : ∀ p ∈ U, primaryPrime p) (hS : ∀ b ∈ S, primary b) :
    (∑ s ∈ U.powerset, ∑ b ∈ S.filter (fun b => (∏ p ∈ s, p) ∣ b), ‖β b‖^2) ≤
        ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hc : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors b).card := by
    exact_mod_cast prime_subset_divisor_count U hU (hS b hb)
  exact mul_le_mul_of_nonneg_right
    (hc.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)) (sq_nonneg _)

lemma bounded_third_divisor_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N M : ℝ), Real.exp 1 ≤ N → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) ≤
        K*M^2*N*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := squarefree_divisor_third_moment hpnt
  refine ⟨K,d,hK,?_⟩
  intro S β N M hN _hM hS hβ
  calc
    _ ≤ ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*M^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ b hb) 2) (by positivity)
    _ = (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card)*M^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ (K*N*(1+Real.log N)^d)*M^2 :=
      mul_le_mul_of_nonneg_right (hbound N S hN hS) (sq_nonneg M)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI

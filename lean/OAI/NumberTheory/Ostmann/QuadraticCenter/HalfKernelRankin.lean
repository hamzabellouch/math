import OAI.NumberTheory.Ostmann.Supply.SquarefreeEulerBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.HalfKernel

namespace OAI

/-! # Rankin's bound for the reciprocal mass of high-weight half kernels -/

namespace Ostmann

open scoped BigOperators

theorem high_weight_squarefree_reciprocal (S P : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (u t : ℝ) (hu : 0 ≤ u) (ht : 1 ≤ t) (b : ℕ)
    (hb : ∀ s ∈ S, b ≤ s.primeFactors.card) :
    (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤
      (t ^ b)⁻¹ * Real.exp (u * t * ∑ p ∈ P, (p : ℝ)⁻¹) := by
  have htb : 0 < t ^ b := pow_pos (lt_of_lt_of_le zero_lt_one ht) _
  calc
    _ ≤ (t ^ b)⁻¹ * ∑ s ∈ S, (u * t) ^ s.primeFactors.card / (s : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ htb).mpr
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (hb s hs))
        (show 0 ≤ u ^ s.primeFactors.card / (s : ℝ) by positivity)
      calc
        _ = t ^ b * (u ^ s.primeFactors.card / (s : ℝ)) := by ring
        _ ≤ t ^ s.primeFactors.card * (u ^ s.primeFactors.card / (s : ℝ)) := hp
        _ = _ := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (squarefree_weighted_reciprocal_le_exp S P hS hP (u * t) (by positivity)) (by positivity)

/-- The exponential high-weight condition forces many factors in the small
half kernel. -/
theorem high_weight_half_kernel_card (s r : ℕ)
    (hcard : r.primeFactors.card = s.primeFactors.card / 2)
    (u K τ : ℝ) (hu : 1 < u) (hhigh : Real.exp (τ * K) < u ^ s.primeFactors.card) :
    τ * K / (2 * Real.log u) - 1 ≤ r.primeFactors.card := by
  have hlog : 0 < Real.log u := Real.log_pos hu
  have hh := Real.log_lt_log (Real.exp_pos _) hhigh
  rw [Real.log_exp, Real.log_pow] at hh
  have hc : s.primeFactors.card ≤ 2 * r.primeFactors.card + 1 := by omega
  have hcR : (s.primeFactors.card : ℝ) ≤ 2 * r.primeFactors.card + 1 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hcR hlog.le
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log u)).mpr
  nlinarith

end Ostmann

end OAI

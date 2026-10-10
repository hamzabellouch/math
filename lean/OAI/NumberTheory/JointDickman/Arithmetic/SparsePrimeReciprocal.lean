import OAI.NumberTheory.JointDickman.Analysis.SparsePrimeMellin
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeReciprocalSquareMass
import OAI.NumberTheory.TwoPointCorrelations.Basic

namespace OAI

/-! # Sparse reciprocal-prime polynomials and their two logarithmic savings -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology

/-- The prime density in both the sampling matrix and its coefficient mass
gives the squared-logarithm saving required for the exceptional class. -/
theorem sparse_prime_reciprocal_sampling (B : ℝ) (hB : 1 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ q : ℕ in atTop, ∀ (N : ℝ) (Q : Finset ℕ) (S : Finset ℝ),
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ Q, p.Prime ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      (S.card:ℝ) ≤ (q:ℝ)^κ →
      ∀ f : ℕ → ℂ, OneBounded f →
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q (fun p => f p/(p:ℂ))
        (fun n => -Real.log (n:ℝ)) t‖^2) ≤ C/(Real.log N)^2 := by
  obtain ⟨C,κ,hC,hκ,hbound⟩ := sparse_prime_mellin_sampling B hB
  obtain ⟨D,hD,hmass⟩ := prime_reciprocal_square_mass
  refine ⟨C*D,κ,mul_pos hC hD,hκ,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with q hq hq2
  intro N Q S hNlo hNhi hQ hsep hdiam hcard f hf
  have hqr : (2:ℝ) ≤ q := by exact_mod_cast hq2
  have hN2 : 2 ≤ N := by
    have hh : (q:ℝ) ≤ (q:ℝ)^10 := le_self_pow₀ (by linarith) (by norm_num)
    exact hqr.trans (hh.trans hNlo)
  have hN0 : 0 < N := by linarith
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hm : (∑ p ∈ Q, ‖f p/(p:ℂ)‖^2) ≤ D/(N*Real.log N) := by
    apply le_trans (b := ∑ p ∈ Q, 1/(p:ℝ)^2)
    · apply sum_le_sum
      intro p hp
      rw [norm_div, Complex.norm_natCast, div_pow]
      exact div_le_div_of_nonneg_right
        (by nlinarith [hf p (hQ p hp).1.pos, norm_nonneg (f p)]) (sq_nonneg _)
    · exact hmass N hN2 Q hQ
  apply (hq N Q S hNlo hNhi hQ hsep hdiam hcard _).trans
  calc
    _ ≤ C*N/Real.log N*(D/(N*Real.log N)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp

end JointDickman

end OAI

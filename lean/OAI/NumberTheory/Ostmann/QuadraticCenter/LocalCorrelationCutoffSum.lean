import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationCutoff
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationInterval
import OAI.NumberTheory.Ostmann.QuadraticCenter.LocalCorrelationSmoothing

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators ComplexConjugate

theorem periodic_interval_cutoff_bound {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ h, ‖normalizedCoefficient F h‖ ≤ A)
    (α : ℝ) (a : ℤ) (N : ℕ) (c c' : ℝ) :
    ‖∑ n ∈ Finset.range N,
      (F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α)) *
        correlationCutoffWeight c c' ((a : ℝ) + n)‖ ≤
      A * (2 * N + 2 * q * (harmonic q : ℝ)) * cutoffFourierBound ^ 2 *
        (1 + (|c| + |c'|) * N) := by
  have hh : 0 ≤ (harmonic q : ℝ) := by unfold harmonic; positivity
  have hB : 0 ≤ A * (2 * N + 2 * q * (harmonic q : ℝ)) := by positivity
  have hp (M : ℕ) (hM : M ≤ N) :
      ‖∑ n ∈ Finset.range M,
        F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α)‖ ≤
      A * (2 * N + 2 * q * (harmonic q : ℝ)) := by
    apply (periodic_interval_twist_bound F hA hcoeff α a M).trans
    gcongr
  have h := finite_abel_norm_bound
    (fun n => F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α))
    (fun n => correlationCutoffWeight c c' ((a : ℝ) + n)) N hB hp
  apply h.trans
  calc
    _ ≤ (A * (2 * N + 2 * q * (harmonic q : ℝ))) *
      (cutoffFourierBound ^ 2 + cutoffFourierBound ^ 2 * (|c| + |c'|) * N) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact add_le_add (norm_correlationCutoffWeight_le _ _ _)
        (correlationCutoffWeight_variation_le c c' (a:ℝ) N)
    _ = _ := by ring

theorem periodic_interval_cutoff_bound_dyadic {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ h, ‖normalizedCoefficient F h‖ ≤ A)
    (α : ℝ) (a : ℤ) (N : ℕ) {c c' S : ℝ}
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hN : (N : ℝ) ≤ S)
    (hs : c*S ≤ 1/4) (hs' : c'*S ≤ 1/4) :
    ‖∑ n ∈ Finset.range N,
      (F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α)) *
        correlationCutoffWeight c c' ((a : ℝ) + n)‖ ≤
      2 * cutoffFourierBound ^ 2 * A * (2 * N + 2 * q * (harmonic q : ℝ)) := by
  have hh : 0 ≤ (harmonic q : ℝ) := by unfold harmonic; positivity
  have hsmall : 1 + (|c| + |c'|) * (N : ℝ) ≤ 2 := by
    rw [abs_of_nonneg hc, abs_of_nonneg hc']
    have h1 := mul_le_mul_of_nonneg_left hN hc
    have h2 := mul_le_mul_of_nonneg_left hN hc'
    nlinarith
  apply (periodic_interval_cutoff_bound F hA hcoeff α a N c c').trans
  calc
    _ ≤ A * (2 * N + 2 * q * (harmonic q : ℝ)) * cutoffFourierBound ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by ring

theorem periodic_interval_cutoff_bound_of_support {q : ℕ} [NeZero q]
    (F : ZMod q → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ h, ‖normalizedCoefficient F h‖ ≤ A)
    (α : ℝ) (a : ℤ) (N : ℕ) {c c' S : ℝ}
    (hc : 0 ≤ c) (hc' : 0 ≤ c') (hN : (N : ℝ) ≤ S) (ha : S ≤ (a : ℝ)) :
    ‖∑ n ∈ Finset.range N,
      (F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α)) *
        correlationCutoffWeight c c' ((a : ℝ) + n)‖ ≤
      2 * cutoffFourierBound ^ 2 * A * (2 * N + 2 * q * (harmonic q : ℝ)) := by
  have hh : 0 ≤ (harmonic q : ℝ) := by unfold harmonic; positivity
  by_cases hzero : ∀ n ∈ Finset.range N, correlationCutoffWeight c c' ((a:ℝ)+n) = 0
  · have hz : (∑ n ∈ Finset.range N,
        (F ((a + (n : ℤ) : ℤ) : ZMod q) * weylPhase (((a : ℝ) + n) * α)) *
          correlationCutoffWeight c c' ((a : ℝ) + n)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [hzero n hn, mul_zero]
    rw [hz, norm_zero]
    positivity
  · push Not at hzero
    obtain ⟨n, hn, hnonzero⟩ := hzero
    have hS : 0 ≤ S := (Nat.cast_nonneg N).trans hN
    have ht : S ≤ (a:ℝ) + n := ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))
    have hb := correlationCutoffWeight_support hnonzero
    rw [abs_of_nonneg (mul_nonneg hc (hS.trans ht)),
      abs_of_nonneg (mul_nonneg hc' (hS.trans ht))] at hb
    apply periodic_interval_cutoff_bound_dyadic F hA hcoeff α a N hc hc' hN
    · exact (mul_le_mul_of_nonneg_left ht hc).trans hb.1.le
    · exact (mul_le_mul_of_nonneg_left ht hc').trans hb.2.le

end Ostmann.QuadraticCenter

end

end OAI

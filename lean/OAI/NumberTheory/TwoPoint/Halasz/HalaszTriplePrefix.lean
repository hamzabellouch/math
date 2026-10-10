import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothSeries
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleConvolution

namespace OAI

/-! Identify a grouped piece of the adaptive double convolution with the
actual coefficients to which narrow Perron inversion is applied. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical LSeries.notation

lemma halasz_convolution_prefix (a b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (a ⍟ b) n) =
      ∑ p ∈ Icc 1 N, a p * ∑ m ∈ Icc 1 (N / p), b m := by
  simp_rw [LSeries.convolution_def]
  rw [halasz_sum_divisorsAntidiagonal (fun p m => a p * b m) N,
    halasz_hyperbola_rows (fun p m => a p * b m) N]
  exact sum_congr rfl (fun p _ => (mul_sum _ _ _).symm)

lemma halasz_finite_convolution_prefix (P : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ)
    (hP : P ⊆ Icc 1 N) :
    (∑ n ∈ Icc 1 N, (halaszFiniteCoefficient P a ⍟ b) n) =
      ∑ p ∈ P, a p * ∑ m ∈ Icc 1 (N / p), b m := by
  rw [halasz_convolution_prefix]
  rw [← sum_subset hP (fun p _ hp => by simp [halaszFiniteCoefficient, hp])]
  apply sum_congr rfl
  intro p hp
  simp [halaszFiniteCoefficient, hp]

lemma halasz_prime_smooth_prefix (f : ℕ → ℂ) (N M : ℕ) (hMN : M ≤ N)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q, q.Prime → q ≤ M → q ∈ Q) :
    (∑ n ∈ Icc 1 M,
      (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * f q) ⍟
        halaszSmoothFunction f N) n) = halaszPrimeConvolution f M := by
  rw [halasz_convolution_prefix, halaszPrimeConvolution, sum_filter]
  apply sum_congr rfl
  intro p hp
  have hpM := (mem_Icc.mp hp).2
  have hs : (∑ m ∈ Icc 1 (M / p), halaszSmoothFunction f N m) =
      ∑ m ∈ Icc 1 (M / p), f m := by
    apply sum_congr rfl
    intro m hm
    exact halasz_smooth_function_eq (mem_Icc.mp hm).1
      (((mem_Icc.mp hm).2.trans (Nat.div_le_self M p)).trans hMN)
  rw [hs]
  by_cases hprime : p.Prime
  · simp [halaszFiniteCoefficient, hcover p hprime hpM, hprime]
  · have hpQ : p ∉ Q := fun h => hprime (hQ p h)
    simp [halaszFiniteCoefficient, hpQ, hprime]

theorem halasz_grouped_triple_prefix (f : ℕ → ℂ) (N : ℕ) (P Q : Finset ℕ)
    (hP : P ⊆ Icc 1 N) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ p ∈ P, ∀ q, q.Prime → q ≤ N / p → q ∈ Q) :
    (∑ n ∈ Icc 1 N,
      (halaszFiniteCoefficient P
          (fun p => (Real.log (p : ℝ) : ℂ) * f p / (Real.log ((N : ℝ) / p) : ℂ)) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q : ℝ) : ℂ) * f q) ⍟
          halaszSmoothFunction f N)) n) =
      ∑ p ∈ P, (Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ)) := by
  rw [halasz_finite_convolution_prefix P _ _ N hP]
  apply sum_congr rfl
  intro p hp
  rw [halasz_prime_smooth_prefix f N (N / p) (Nat.div_le_self N p) Q hQ (hcover p hp)]
  ring

lemma halasz_smooth_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    OneBounded (halaszSmoothFunction f N) := by
  intro n hn
  unfold halaszSmoothFunction
  split_ifs
  · exact hf n hn
  · simp

end TwoPointCorrelations

end OAI

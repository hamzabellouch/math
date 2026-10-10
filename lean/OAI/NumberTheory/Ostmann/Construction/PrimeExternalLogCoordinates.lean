import OAI.NumberTheory.Ostmann.Construction.SmoothGiantExternalAverage
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernel

namespace OAI

/-! # Exact positive-log cutoffs at the prime points of the exterior law -/

namespace Ostmann
open scoped Classical BigOperators

theorem primeExternalAverage_congr_primes {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ s y (p q : ℕ), p.Prime → q.Prime →
      F s y (Real.log p) (Real.log q) = H s y (Real.log p) (Real.log q)) :
    primeExternalAverage ν N u v r w F = primeExternalAverage ν N u v r w H := by
  unfold primeExternalAverage
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg (fun z : ℂ => ((∏ i, ν i (y i) : ℝ) : ℂ) * z)
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro q _
  simp only [Nat.modEq_one, and_true]
  by_cases hq : q.Prime
  · rw [ite_eq_left hq, ite_eq_left hq]
    apply congrArg (fun z : ℂ => z * ((q : ℝ)⁻¹ : ℂ))
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime
    · rw [ite_eq_left hp, ite_eq_left hp, h s.val y p q hp hq]
    · rw [ite_eq_right hp, ite_eq_right hp]
  · rw [ite_eq_right hq, ite_eq_right hq]

theorem primeExternalAverage_log_cutoff {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w G H : ℝ) (φ : ℝ → ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    primeExternalAverage ν N u v r w (fun s y x z =>
      (positiveLogCutoff φ G ⌊Real.exp x⌋₊ : ℂ) *
        (positiveLogCutoff φ H ⌊Real.exp z⌋₊ : ℂ) *
          F s y (Real.log ⌊Real.exp x⌋₊) (Real.log ⌊Real.exp z⌋₊)) =
    primeExternalAverage ν N u v r w (fun s y x z =>
      (φ (x - G) : ℂ) * (φ (z - H) : ℂ) * F s y x z) := by
  refine primeExternalAverage_congr_primes ν N u v r w _ _ ?_
  intro s y p q hp hq
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  simp only [Real.exp_log hp', Real.exp_log hq', Nat.floor_natCast,
    positiveLogCutoff, hp', hq', ite_true]

/-- This is the normalized original giant law written with the same
positive-log outer factors as the moving statistic. -/
theorem smoothGiantExternalAverage_log_cutoff {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    smoothGiantExternalAverage ν N φ G H
      (fun s y p q => F s y (Real.log p) (Real.log q)) =
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      primeExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) (fun s y x z =>
        (positiveLogCutoff φ G ⌊Real.exp x⌋₊ : ℂ) *
          (positiveLogCutoff φ H ⌊Real.exp z⌋₊ : ℂ) *
            F s y (Real.log ⌊Real.exp x⌋₊) (Real.log ⌊Real.exp z⌋₊)) := by
  rw [smoothGiantExternalAverage_eq ν N φ G H hout]
  apply congrArg (fun z : ℂ =>
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
      smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) * z)
  refine primeExternalAverage_congr_primes ν N (G - 1) (G + 1) (H - 1) (H + 1) _ _ ?_
  intro s y p q hp hq
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  simp only [Real.exp_log hp', Real.exp_log hq', Nat.floor_natCast,
    positiveLogCutoff, hp', hq', ite_true]

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.SmoothGiantIntervalBridge
import OAI.NumberTheory.Ostmann.Characters.MixedExternalAverage

namespace OAI

/-! # Exact transport of the smooth integer/prime pair, with both scale factors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The integer coordinate has its original counting weight. Passing to the
logarithmic cell introduces exactly the displayed exponential scale. -/
theorem smoothInteger_interval (φ : ℝ → ℝ) (G center : ℝ) (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
      (φ (Real.log p - G) : ℂ) * F p) =
    (Real.exp center : ℂ) * complexIntegerInterval 1 0 (G - 1) (G + 1) center
      (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊) := by
  unfold complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  simp only [integerResidueAtom, Nat.modEq_one, ite_true, Real.exp_log hp0, Nat.floor_natCast]
  have he : (Real.exp center : ℂ) * (Real.exp (-center) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = ((φ (Real.log p - G) : ℂ) * F p) * 1 := (mul_one _).symm
    _ = ((φ (Real.log p - G) : ℂ) * F p) *
        ((Real.exp center : ℂ) * (Real.exp (-center) : ℂ)) := by rw [he]
    _ = _ := by ring

/-- The remaining giant is averaged with its original normalized harmonic
prior; no endpoint prime is deleted. -/
theorem smoothGiant_integer_interval (φ : ℝ → ℝ) (G H center : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℕ → ℂ) :
    (∑ q : smoothGiantPrimeRange H,
      (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
        ∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
          (φ (Real.log p - G) : ℂ) * F p q) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + center) : ℂ) *
      complexPrimeInterval 1 0 (H - 1) (H + 1) (fun y =>
        complexIntegerInterval 1 0 (G - 1) (G + 1) center (fun x =>
          (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
  rw [smoothGiantPrior_interval φ H hout (fun q =>
    ∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
      (φ (Real.log p - G) : ℂ) * F p q)]
  have hp (q : ℕ) := smoothInteger_interval φ G center (fun p => F p q)
  simp_rw [hp]
  have hf : (fun y => (φ (y - H) : ℂ) *
      ((Real.exp center : ℂ) * complexIntegerInterval 1 0 (G - 1) (G + 1) center
        (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))) =
    (fun y => (Real.exp center : ℂ) * complexIntegerInterval 1 0 (G - 1) (G + 1) center
        (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
    funext y
    rw [show (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊) =
        (fun x => (φ (y - H) : ℂ) * ((φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) from
      funext (fun _ => by ring), complexIntegerInterval_const_mul]
    ring
  rw [hf, complexPrimeInterval_const_mul, Real.exp_add, Complex.ofReal_mul]
  ring

/-- Finite Fubini retains the original regular law and counting measure on
frequencies, as well as the exact giant and integer normalizations. -/
theorem smoothGiant_mixed_external_interval {A B : Type*} [Fintype A] [Fintype B]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H center : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (F : ℤ → (B → A) → ℕ → ℕ → ℂ) :
    (∑ s : transferFrequencyRange N, ∑ x : B → A, ((∏ i, ν i (x i) : ℝ) : ℂ) *
      ∑ q : smoothGiantPrimeRange H,
        (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
          ∑ p ∈ Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊,
            (φ (Real.log p - G) : ℂ) * F s.val x p q) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H + center) : ℂ) *
      mixedExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1) center
        (fun s x z y => (φ (z - G) : ℂ) * (φ (y - H) : ℂ) *
          F s x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊) := by
  unfold mixedExternalAverage
  have hpair (s : ℤ) (x : B → A) := smoothGiant_integer_interval φ G H center hout (F s x)
  simp_rw [hpair]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  ring

end Ostmann

end OAI

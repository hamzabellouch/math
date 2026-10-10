import OAI.NumberTheory.Ostmann.Construction.SmoothGiantIntervalBridge

namespace OAI

/-! # The two original normalized giant priors in the exterior average -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_pair_interval (φ : ℝ → ℝ) (G H : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℕ → ℕ → ℂ) :
    (∑ q : smoothGiantPrimeRange H,
      (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
        ∑ p : smoothGiantPrimeRange G,
          (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p q) =
    (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
      smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      complexPrimeInterval 1 0 (H - 1) (H + 1) (fun y =>
        complexPrimeInterval 1 0 (G - 1) (G + 1) (fun x =>
          (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
  rw [smoothGiantPrior_interval φ H hout (fun q : ℕ =>
    ∑ p : smoothGiantPrimeRange G,
      (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) * F p q)]
  have hG (q : ℕ) := smoothGiantPrior_interval φ G hout (fun p => F p q)
  simp_rw [hG]
  have hf : (fun y => (φ (y - H) : ℂ) *
      ((Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
        complexPrimeInterval 1 0 (G - 1) (G + 1)
          (fun x => (φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))) =
    (fun y => (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) : ℂ) *
      complexPrimeInterval 1 0 (G - 1) (G + 1)
        (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) := by
    funext y
    rw [show (fun x => (φ (x - G) : ℂ) * (φ (y - H) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊) =
      (fun x => (φ (y - H) : ℂ) * ((φ (x - G) : ℂ) * F ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) from
      funext (fun _ => by ring), complexPrimeInterval_const_mul]
    ring
  rw [hf, complexPrimeInterval_const_mul, Real.exp_add, Complex.ofReal_mul]
  ring

noncomputable def smoothGiantExternalAverage {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H : ℝ)
    (F : ℤ → (B → A) → ℕ → ℕ → ℂ) : ℂ :=
  ∑ s : transferFrequencyRange N, ∑ y : B → A, ((∏ i, ν i (y i) : ℝ) : ℂ) *
    ∑ q : smoothGiantPrimeRange H, (smoothGiantPrior (smoothGiantPrimeRange H) φ H q : ℂ) *
      ∑ p : smoothGiantPrimeRange G, (smoothGiantPrior (smoothGiantPrimeRange G) φ G p : ℂ) *
        F s.val y p q

theorem smoothGiantExternalAverage_eq {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℤ → (B → A) → ℕ → ℕ → ℂ) :
    smoothGiantExternalAverage ν N φ G H F =
      (Real.exp (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H) : ℂ) *
      primeExternalAverage ν N (G - 1) (G + 1) (H - 1) (H + 1)
        (fun s y x z => (φ (x - G) : ℂ) * (φ (z - H) : ℂ) * F s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) := by
  unfold smoothGiantExternalAverage primeExternalAverage
  have hp (s : ℤ) (y : B → A) := smoothGiantPrior_pair_interval φ G H hout (F s y)
  simp_rw [hp]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The unit-rectangle bounds apply to the original normalized giant law
with the exact two normalizers and the fixed four-rectangle cost. -/
theorem smoothGiantExternalAverage_full_cell_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (φ : ℝ → ℝ) (G H E : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (F : ℤ → (B → A) → ℕ → ℕ → ℂ)
    (h : ∀ i j : Bool, ‖primeExternalAverage ν N
      (if i then G else G - 1) ((if i then G else G - 1) + 1)
      (if j then H else H - 1) ((if j then H else H - 1) + 1)
      (fun s y x z => (φ (x - G) : ℂ) * (φ (z - H) : ℂ) *
        F s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)‖ ^ 2 ≤ E) :
    ‖smoothGiantExternalAverage ν N φ G H F‖ ^ 2 ≤
      16 * Real.exp (2 * (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G +
        smoothGiantLogNormalizer (smoothGiantPrimeRange H) φ H)) * E := by
  have hb := primeExternalAverage_full_cell_bound ν N G H E
    (fun s y x z => (φ (x - G) : ℂ) * (φ (z - H) : ℂ) *
      F s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊) h
  rw [smoothGiantExternalAverage_eq ν N φ G H hout F, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow]
  have he (z : ℝ) : Real.exp z ^ 2 = Real.exp (2 * z) := by
    rw [← Real.exp_nat_mul]
    congr 1
  rw [he]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)).trans_eq (by ring)

end Ostmann

end OAI

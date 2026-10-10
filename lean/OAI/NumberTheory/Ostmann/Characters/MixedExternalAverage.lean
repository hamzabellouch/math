import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalMatchedCorrelation
import OAI.NumberTheory.Ostmann.Construction.SelectedBulkPermutation
import OAI.NumberTheory.Ostmann.Preliminaries.WeightedNormTriangle

namespace OAI

/-! # The original root, prime and integer average as one finite positive law -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MixedExternalPoint (B A : Type*) (N : ℕ) (u v r w : ℝ) :=
  transferFrequencyRange N × (B → A) ×
    (Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp w⌋₊) × (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊)

noncomputable def mixedExternalPrior {B A : Type*} [Fintype B]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (x : MixedExternalPoint B A N u v r w) : ℝ :=
  (∏ b, ν b (x.2.1 b)) *
    (if (x.2.2.1.val).Prime then (x.2.2.1.val : ℝ)⁻¹ else 0) *
      integerResidueAtom 1 0 center x.2.2.2.val

noncomputable def mixedExternalAverage {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) : ℂ :=
  ∑ s : transferFrequencyRange N, ∑ y : B → A, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z =>
      complexIntegerInterval 1 0 u v center (fun x => F s.val y x z))

theorem mixedExternalPrior_nonneg {B A : Type*} [Fintype B]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ) (x : MixedExternalPoint B A N u v r w) :
    0 ≤ mixedExternalPrior ν N u v r w center x := by
  unfold mixedExternalPrior
  apply mul_nonneg
  · exact mul_nonneg (Finset.prod_nonneg fun b _ => hν b _) (by split_ifs <;> positivity)
  · exact integerResidueAtom_nonneg 1 0 center _

theorem mixedExternalAverage_finite {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center F =
      ∑ x : MixedExternalPoint B A N u v r w,
        (mixedExternalPrior ν N u v r w center x : ℂ) *
          F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val) := by
  have hp (F : ℝ → ℂ) : complexPrimeInterval 1 0 r w F =
      ∑ p : Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp w⌋₊,
        if (p.val).Prime then F (Real.log p.val) * ((p.val : ℝ)⁻¹ : ℂ) else 0 := by
    rw [Finset.sum_coe_sort _ (fun p : ℕ =>
      if p.Prime then F (Real.log p) * ((p : ℝ)⁻¹ : ℂ) else 0)]
    simp only [complexPrimeInterval, Nat.modEq_one, and_true]
  have hi (F : ℝ → ℂ) : complexIntegerInterval 1 0 u v center F =
      ∑ q : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        F (Real.log q.val) * (integerResidueAtom 1 0 center q.val : ℂ) := by
    rw [Finset.sum_coe_sort _ (fun q : ℕ =>
      F (Real.log q) * (integerResidueAtom 1 0 center q : ℂ))]
    rfl
  simp only [mixedExternalAverage, hp, hi, MixedExternalPoint,
    Fintype.sum_prod_type, mixedExternalPrior]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hprime : (p.val).Prime
  · simp only [hprime, ite_true, Complex.ofReal_mul]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    push_cast
    ring
  · simp only [hprime, ite_false, mul_zero, zero_mul, Complex.ofReal_zero,
      Finset.sum_const_zero]

theorem mixedExternalAverage_star {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    mixedExternalAverage ν N u v r w center (fun s y x z => star (F s y x z)) =
      star (mixedExternalAverage ν N u v r w center F) := by
  simp [mixedExternalAverage_finite]

theorem mixedExternalAverage_correlation_le {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => F s y x z * star (H s y x z))‖ ≤
      Real.sqrt (mixedExternalAverage ν N u v r w center
        (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ))).re *
      Real.sqrt (mixedExternalAverage ν N u v r w center
        (fun s y x z => (‖H s y x z‖ ^ 2 : ℂ))).re := by
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.star_def,
    ← Complex.ofReal_pow]
  exact weighted_correlation_le_sqrt_energy Finset.univ
    (mixedExternalPrior ν N u v r w center)
    (fun x => F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val))
    (fun x => H x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val))
    (fun x _ => mixedExternalPrior_nonneg ν hν N u v r w center x)

end Ostmann

end OAI

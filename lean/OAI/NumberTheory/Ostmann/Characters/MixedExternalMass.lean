import OAI.NumberTheory.Ostmann.Characters.MixedExternalStatistic
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueIntervals
import OAI.NumberTheory.Ostmann.Construction.RoundedEnergyCutoffs

namespace OAI

/-! # Elementary total-mass bounds for the original mixed external law -/

namespace Ostmann
open scoped Classical BigOperators

theorem complexIntegerInterval_const (u v center : ℝ) (c : ℂ) :
    complexIntegerInterval 1 0 u v center (fun _ => c) =
      (integerLogCellMass 1 0 u v center : ℂ) * c := by
  simp only [complexIntegerInterval, integerLogCellMass, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem complexPrimeInterval_const (r w : ℝ) (c : ℂ) :
    complexPrimeInterval 1 0 r w (fun _ => c) =
      (reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp w) : ℂ) * c := by
  simp only [complexPrimeInterval, reciprocalPrimeInterval, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all [mul_comm]

theorem mixedExternalAverage_const {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hmass : ∀ b, ∑ a, ν b a = 1)
    (N : ℕ) (u v r w center : ℝ) (c : ℂ) :
    mixedExternalAverage ν N u v r w center (fun _ _ _ _ => c) =
      (((2 * N + 1 : ℕ) : ℝ) * reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp w) *
        integerLogCellMass 1 0 u v center : ℝ) * c := by
  simp only [mixedExternalAverage, complexIntegerInterval_const, complexPrimeInterval_const]
  have hν : ∑ y : B → A, (∏ b, ν b (y b) : ℝ) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  simp only [← Finset.sum_mul, ← Complex.ofReal_sum, hν, Complex.ofReal_one, one_mul]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, card_transferFrequencyRange,
    nsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

theorem integerLogCellMass_le_exp (u v center : ℝ) :
    integerLogCellMass 1 0 u v center ≤ Real.exp (v - center) := by
  simp only [integerLogCellMass, integerResidueAtom, Nat.modEq_one, ite_true,
    Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  calc
    _ ≤ Real.exp v * Real.exp (-center) :=
      mul_le_mul_of_nonneg_right
        ((Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (Real.exp_pos _).le))
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, sub_eq_add_neg]

theorem mixedExternalAverage_mass_bound {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a) (hmass : ∀ b, ∑ a, ν b a = 1)
    (N : ℕ) (u v r w center C : ℝ) (hC : 0 ≤ C)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hF : ∀ s y x z, (F s y x z).re ≤ C) :
    (mixedExternalAverage ν N u v r w center F).re ≤
      C * (2 * N + 1 : ℕ) * Real.exp ((w - r) + (v - center)) := by
  have hunit : (mixedExternalAverage ν N u v r w center (fun _ _ _ _ => (1 : ℂ))).re =
      ((2 * N + 1 : ℕ) : ℝ) * reciprocalPrimeInterval 1 0 (Real.exp r) (Real.exp w) *
        integerLogCellMass 1 0 u v center := by
    rw [mixedExternalAverage_const ν hmass]
    simp
  have hbound : (mixedExternalAverage ν N u v r w center F).re ≤
      C * (mixedExternalAverage ν N u v r w center (fun _ _ _ _ => (1 : ℂ))).re := by
    simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_one, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    exact (mul_le_mul_of_nonneg_left (hF _ _ _ _)
      (mixedExternalPrior_nonneg ν hν N u v r w center x)).trans_eq (by ring)
  rw [hunit] at hbound
  apply hbound.trans
  rw [Real.exp_add]
  have hp := reciprocalPrimeInterval_le_exp 1 0 r w
  have hi := integerLogCellMass_le_exp u v center
  have hp0 := reciprocalPrimeInterval_nonneg 1 0 (Real.exp r) (Real.exp w)
  have hi0 := integerLogCellMass_nonneg 1 0 u v center
  nlinarith [mul_le_mul hp hi hi0 (Real.exp_pos _).le,
    mul_nonneg hC (Nat.cast_nonneg (2 * N + 1))]

theorem mixedExternalAverage_re_nonneg {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) (hF : ∀ s y x z, 0 ≤ (F s y x z).re) :
    0 ≤ (mixedExternalAverage ν N u v r w center F).re := by
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg
    (mixedExternalPrior_nonneg ν hν N u v r w center x) (hF _ _ _ _))

theorem mixedExternalAverage_re_mono {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hFH : ∀ s y x z, (F s y x z).re ≤ (H s y x z).re) :
    (mixedExternalAverage ν N u v r w center F).re ≤
      (mixedExternalAverage ν N u v r w center H).re := by
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
    (hFH _ _ _ _) (mixedExternalPrior_nonneg ν hν N u v r w center x))

end Ostmann

end OAI

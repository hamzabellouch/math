import OAI.NumberTheory.JointDickman.Amplification.ArithmeticSquareHits
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteResidues

namespace OAI

/-! # The arithmetic and fair-split weights differ only at rare square hits -/

namespace JointDickman
open Finset

open Classical in
theorem independentWeightedAmplification_le {B L : ℕ} {τ C : ℝ}
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, w a c ≤ 1) {S R : Finset ℕ}
    (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    independentWeightedAmplification B L τ C w S R ≤ B := by
  have hh := sitePairSplitAverage_mono (auxiliaryPrimes B) S R
    (fun A D => if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
      then w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0)
    (fun _ _ => 1) (by intros; split_ifs; exact hw _ _; norm_num)
  rw [sitePairSplitAverage_const_one hS hR] at hh
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg B)).trans_eq (mul_one _)

open Classical in
theorem arithmetic_model_power_error {B L n : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |(arithmeticSubsetAmplification B L τ C w n)^k -
      (independentWeightedAmplification B L τ C w
        (coefficientPrimeSet B n) (coefficientPrimeSet B (n+1)))^k| ≤
      (B : ℝ)^k * (if AuxiliarySquareHit B n then 1 else 0) := by
  by_cases h : AuxiliarySquareHit B n
  · rw [ite_eq_left h, mul_one]
    have ha0 := arithmeticSubsetAmplification_nonneg B L n τ C w (fun a c => (hw a c).1)
    have ha1 := arithmeticSubsetAmplification_le (L := L) τ C hB w (fun a c => (hw a c).2) (n := n)
    have hb0 := independentWeightedAmplification_nonneg B L τ C w (fun a c => (hw a c).1)
      (coefficientPrimeSet B n) (coefficientPrimeSet B (n+1))
    have hb1 := independentWeightedAmplification_le (B := B) (L := L) (τ := τ) (C := C) w (fun a c => (hw a c).2)
      (S := coefficientPrimeSet B n) (R := coefficientPrimeSet B (n+1))
      (filter_subset _ _) (filter_subset _ _)
    have ha := pow_le_pow_left₀ ha0 ha1 k
    have hb := pow_le_pow_left₀ hb0 hb1 k
    have ha' := pow_nonneg ha0 k
    have hb' := pow_nonneg hb0 k
    rw [abs_le]
    constructor <;> linarith
  · have hn : ∀ p ∈ auxiliaryPrimes B, ¬p^2 ∣ n :=
      fun p hp hd => h ⟨p, hp, Or.inl hd⟩
    have hn' : ∀ p ∈ auxiliaryPrimes B, ¬p^2 ∣ n+1 :=
      fun p hp hd => h ⟨p, hp, Or.inr hd⟩
    rw [arithmeticSubsetAmplification_eq_model hB w hn hn', sub_self, abs_zero,
      ite_eq_right h, mul_zero]

end JointDickman

end OAI

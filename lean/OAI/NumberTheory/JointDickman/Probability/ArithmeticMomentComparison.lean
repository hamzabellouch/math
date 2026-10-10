import OAI.NumberTheory.JointDickman.Amplification.ArithmeticModelError

namespace OAI

/-! # Arithmetic amplification moments and the independent model -/

namespace JointDickman
open Finset

noncomputable def arithmeticAmplificationMoment (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ a : ZMod (auxiliarySquarePeriod B),
    (arithmeticSubsetAmplification B L τ C w a.val)^k) / (auxiliarySquarePeriod B : ℝ)

noncomputable def independentAmplificationMoment (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
    ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
      (independentWeightedAmplification B L τ C w S R)^k

open Classical in
theorem arithmeticMoment_square_error {B L : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |arithmeticAmplificationMoment B L τ C w k -
      (∑ a : ZMod (auxiliarySquarePeriod B),
        (independentWeightedAmplification B L τ C w
          (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1)))^k) /
            (auxiliarySquarePeriod B : ℝ)| ≤
      2*(B : ℝ)^k*∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  have hM : (0 : ℝ) < auxiliarySquarePeriod B := by exact_mod_cast auxiliarySquarePeriod_pos B
  unfold arithmeticAmplificationMoment
  rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hM]
  calc
    _ ≤ (∑ a : ZMod (auxiliarySquarePeriod B),
        |(arithmeticSubsetAmplification B L τ C w a.val)^k -
          (independentWeightedAmplification B L τ C w
            (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1)))^k|) /
              (auxiliarySquarePeriod B : ℝ) :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hM.le
    _ ≤ ((B : ℝ)^k * ∑ a : ZMod (auxiliarySquarePeriod B),
        if AuxiliarySquareHit B a.val then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ) := by
      apply div_le_div_of_nonneg_right _ hM.le
      rw [mul_sum]
      exact sum_le_sum (fun a _ => arithmetic_model_power_error hB w hw k)
    _ = (B : ℝ)^k * ((∑ a : ZMod (auxiliarySquarePeriod B),
        if AuxiliarySquareHit B a.val then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ)) := by ring
    _ ≤ (B : ℝ)^k * (2 * ∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (residue_squareHit_mean_bound B) (by positivity)
    _ = _ := by ring

theorem siteMoment_independent_error {B L : ℕ} {τ C : ℝ}
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |(∑ a : ZMod (auxiliarySquarePeriod B),
        (independentWeightedAmplification B L τ C w
          (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1)))^k) /
            (auxiliarySquarePeriod B : ℝ) -
      independentAmplificationMoment B L τ C w k| ≤
      4*(B : ℝ)^k*∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  classical
  let F (S R : Finset ℕ) := (independentWeightedAmplification B L τ C w S R)^k
  have hF (S : Finset ℕ) (hS : S ∈ (auxiliaryPrimes B).powerset)
      (R : Finset ℕ) (hR : R ∈ (auxiliaryPrimes B).powerset) : |F S R| ≤ (B : ℝ)^k := by
    have h0 := independentWeightedAmplification_nonneg B L τ C w (fun a c => (hw a c).1) S R
    have h1 := independentWeightedAmplification_le (B := B) (L := L) (τ := τ) (C := C) w (fun a c => (hw a c).2)
      (mem_powerset.mp hS) (mem_powerset.mp hR)
    rw [abs_of_nonneg (pow_nonneg h0 k)]
    exact pow_le_pow_left₀ h0 h1 k
  have hc := consecutive_site_mean_bound (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    F (by positivity : 0 ≤ (B : ℝ)^k) hF
  have hm := consecutive_site_mean_at_multiple (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (auxiliaryProduct_dvd_period (Subset.refl (auxiliaryPrimes B))) F
  change |(∑ a : ZMod (auxiliarySquarePeriod B),
      F (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1))) /
      (auxiliarySquarePeriod B : ℝ) - _| ≤ _
  rw [show ((∑ a : ZMod (auxiliarySquarePeriod B),
      F (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1))) /
      (auxiliarySquarePeriod B : ℝ)) = _ from hm]
  convert hc using 2
  unfold independentAmplificationMoment
  congr 1
  apply sum_congr rfl
  intro S _
  rw [mul_sum]
  apply sum_congr rfl
  intro R _
  dsimp [F]
  ring

theorem arithmeticMoment_independent_error {B L : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |arithmeticAmplificationMoment B L τ C w k - independentAmplificationMoment B L τ C w k| ≤
      6*(B : ℝ)^k*∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  have h1 := arithmeticMoment_square_error (L := L) (τ := τ) (C := C) hB w hw k
  have h2 := siteMoment_independent_error (B := B) (L := L) (τ := τ) (C := C) w hw k
  exact (abs_sub_le _ _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end JointDickman

end OAI

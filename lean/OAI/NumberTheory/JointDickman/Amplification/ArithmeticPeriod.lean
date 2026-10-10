import OAI.NumberTheory.JointDickman.Amplification.ArithmeticAmplificationBounds
import OAI.NumberTheory.JointDickman.Counting.PeriodicNonnegative

namespace OAI

/-! # The exact finite period of the divisor amplification -/

namespace JointDickman
open Finset

noncomputable def auxiliarySquarePeriod (B : ℕ) : ℕ :=
  (∏ p ∈ auxiliaryPrimes B, p)^2

theorem auxiliarySquarePeriod_pos (B : ℕ) : 0 < auxiliarySquarePeriod B := by
  unfold auxiliarySquarePeriod
  exact pow_pos (prod_pos (fun p hp => (auxiliaryPrimes_prime B p hp).pos)) _

instance (B : ℕ) : NeZero (auxiliarySquarePeriod B) :=
  ⟨(auxiliarySquarePeriod_pos B).ne'⟩

theorem auxiliaryProduct_dvd_period {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : (∏ p ∈ A, p) ∣ auxiliarySquarePeriod B := by
  exact (prod_dvd_prod_of_subset A (auxiliaryPrimes B) id hA).trans (dvd_pow_self _ (by omega))

theorem auxiliaryProduct_mul_prime_dvd_period {B p : ℕ} {A : Finset ℕ}
    (hp : p ∈ auxiliaryPrimes B) (hA : A ⊆ auxiliaryPrimes B) :
    (∏ p ∈ A, p) * p ∣ auxiliarySquarePeriod B := by
  unfold auxiliarySquarePeriod
  rw [pow_two]
  exact Nat.mul_dvd_mul (prod_dvd_prod_of_subset A (auxiliaryPrimes B) id hA)
    (dvd_prod_of_mem id hp)

theorem coefficientPrimeSet_quotient_modEq {B n m : ℕ} {A : Finset ℕ}
    (h : n ≡ m [MOD auxiliarySquarePeriod B]) (hA : A ⊆ auxiliaryPrimes B)
    (ha : (∏ p ∈ A, p) ∣ n) (hb : (∏ p ∈ A, p) ∣ m) :
    coefficientPrimeSet B (n / (∏ p ∈ A, p)) =
      coefficientPrimeSet B (m / (∏ p ∈ A, p)) := by
  ext p
  simp only [coefficientPrimeSet, mem_filter]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, (Nat.dvd_div_iff_mul_dvd hb).mpr ?_⟩
    exact (h.dvd_iff (auxiliaryProduct_mul_prime_dvd_period hp hA)).mp
      ((Nat.dvd_div_iff_mul_dvd ha).mp hn)
  · rintro ⟨hp, hm⟩
    refine ⟨hp, (Nat.dvd_div_iff_mul_dvd ha).mpr ?_⟩
    exact (h.dvd_iff (auxiliaryProduct_mul_prime_dvd_period hp hA)).mpr
      ((Nat.dvd_div_iff_mul_dvd hb).mp hm)

open Classical in
theorem arithmeticSubsetAmplification_modEq {B L n m : ℕ} (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (h : n ≡ m [MOD auxiliarySquarePeriod B]) :
    arithmeticSubsetAmplification B L τ C w n =
      arithmeticSubsetAmplification B L τ C w m := by
  unfold arithmeticSubsetAmplification
  congr 1
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  have hAP := mem_powerset.mp hA
  have hDP := mem_powerset.mp hD
  have ha := h.dvd_iff (auxiliaryProduct_dvd_period hAP)
  have hd := (h.add_right 1).dvd_iff (auxiliaryProduct_dvd_period hDP)
  by_cases hn : (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n + 1
  · have hm := And.intro (ha.mp hn.1) (hd.mp hn.2)
    rw [ite_eq_left hn, ite_eq_left hm,
      coefficientPrimeSet_quotient_modEq h hAP hn.1 hm.1,
      coefficientPrimeSet_quotient_modEq (h.add_right 1) hDP hn.2 hm.2]
  · have hm : ¬ ((∏ p ∈ A, p) ∣ m ∧ (∏ p ∈ D, p) ∣ m + 1) :=
      fun hm => hn ⟨ha.mpr hm.1, hd.mpr hm.2⟩
    rw [ite_eq_right hn, ite_eq_right hm]

open Classical in
noncomputable def residueAmplification (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ)
    (a : ZMod (auxiliarySquarePeriod B)) : ℝ :=
  arithmeticSubsetAmplification B L τ C w a.val

theorem residueAmplification_natCast (B L n : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    residueAmplification B L τ C w n = arithmeticSubsetAmplification B L τ C w n := by
  unfold residueAmplification
  rw [ZMod.val_natCast]
  exact arithmeticSubsetAmplification_modEq τ C w (Nat.mod_modEq _ _)

/-- The ordinary mean has this exact finite residue mean as its limit. -/
theorem arithmeticAmplification_mean_tendsto (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    Filter.Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, arithmeticSubsetAmplification B L τ C w n) / (N : ℝ))
      Filter.atTop (nhds ((∑ a : ZMod (auxiliarySquarePeriod B),
        residueAmplification B L τ C w a) / (auxiliarySquarePeriod B : ℝ))) := by
  have h := periodicAverage_tendsto (fun a => (residueAmplification B L τ C w a : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, periodicAverage, residueMean, residueAmplification_natCast,
    Complex.div_natCast_re, Complex.re_sum, Complex.ofReal_re] using hr

end JointDickman

end OAI

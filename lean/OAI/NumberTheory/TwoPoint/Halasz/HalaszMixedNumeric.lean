import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedDouble
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleMean

namespace OAI

/-! The cost of deleting primes below the upper endpoint of the typical
bands, before applying the mixed Perron estimate. -/

namespace TwoPointCorrelations

open Finset

noncomputable def halaszMixedNumericConstant : ℝ :=
  (halaszPrimePowerConstant+3*halaszMertensConstant+1+Real.log 2+1)+
    (halaszPrimePowerConstant+halaszMertensConstant+1+Real.log 2+1)*
      (1+|halaszDenominatorConstant|)

lemma halaszMixedNumericConstant_nonneg : 0 ≤ halaszMixedNumericConstant := by
  have := halaszPrimePowerConstant_nonneg
  have := halaszMertensConstant_nonneg
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold halaszMixedNumericConstant
  positivity

lemma halasz_mixed_mean_numeric (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2)
    (hll : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖ ≤ ‖halaszMixedDouble G B N R‖ +
      halaszMixedNumericConstant*(N:ℝ)*(1+Real.log R)*Real.log (Real.log N) := by
  have hh := halasz_mixed_double_mean G B hG hB N hR hRN hmul
  let A := halaszPrimePowerConstant+3*halaszMertensConstant+1+Real.log 2
  let E := halaszPrimePowerConstant+halaszMertensConstant+1+Real.log 2
  let r := Real.log R
  let l := Real.log (Real.log (N:ℝ))
  have hA : 0 ≤ A := by
    dsimp [A]
    have := halaszPrimePowerConstant_nonneg
    have := halaszMertensConstant_nonneg
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    have := halaszPrimePowerConstant_nonneg
    have := halaszMertensConstant_nonneg
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hr : 0 ≤ r := Real.log_nonneg hR
  have hl : 1 ≤ l := hll
  have hb : A+r ≤ (A+1)*(1+r)*l := by
    calc
      _ ≤ (A+1)*(1+r) := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hl
  have he : E+r ≤ (E+1)*(1+r) := by nlinarith
  have hd : l+halaszDenominatorConstant ≤ (1+|halaszDenominatorConstant|)*l := by
    have ha := le_abs_self halaszDenominatorConstant
    have hb := le_mul_of_one_le_right (abs_nonneg halaszDenominatorConstant) hl
    nlinarith
  have hc : (E+r)*(l+halaszDenominatorConstant) ≤
      ((E+1)*(1+r))*((1+|halaszDenominatorConstant|)*l) := by
    calc
      _ ≤ (E+r)*((1+|halaszDenominatorConstant|)*l) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)
  have hs : A+r+(E+r)*(l+halaszDenominatorConstant) ≤
      halaszMixedNumericConstant*(1+r)*l := by
    dsimp [halaszMixedNumericConstant]
    change A+r+(E+r)*(l+halaszDenominatorConstant) ≤
      ((A+1)+(E+1)*(1+|halaszDenominatorConstant|))*(1+r)*l
    nlinarith
  have hn := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N : (0:ℝ)≤N)
  dsimp [halaszMixedErrorConstant] at hh
  dsimp [A,E,r,l,halaszDenominatorConstant] at hn
  nlinarith

end TwoPointCorrelations

end OAI

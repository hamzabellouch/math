import Mathlib.Analysis.Complex.ExponentialBounds
import OAI.NumberTheory.Ostmann.ZeroDensity.RealZeroPairExclusion

namespace OAI

/-! # Page uniqueness for the actual primitive real zeros

The one-pole bound for two distinct characters and positivity of the actual
zero sums give an absolute Landau–Page constant. No uniqueness input is used.
-/

namespace Ostmann

open Complex

theorem exists_actual_page_uniqueness : ∃ κ : ℝ, 0 < κ ∧
    ∀ Q : ℕ, 2 ≤ Q → ∀ e f : PrimitiveRealZero,
      e.modulus ≤ Q → f.modulus ≤ Q →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ e.beta →
      1 - κ / Real.log (4 * (Q : ℝ)) ≤ f.beta → e = f := by
  obtain ⟨R, hR, hsingle⟩ := exists_real_zero_sum_upper
  obtain ⟨S, hS, hpair⟩ := exists_distinct_real_zero_sum_bound
  let D : ℝ := R + S + 10
  have hD : 0 < D := by dsimp [D]; positivity
  let κ : ℝ := 1 / (2000 * D)
  refine ⟨κ, by dsimp [κ]; positivity, ?_⟩
  intro Q hQ e f he hf hbe hbf
  let H : ℝ := Real.log (4 * (Q : ℝ))
  have hQr : 2 ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hH : 1 ≤ H := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < 4 * (Q : ℝ))).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hHpos : 0 < H := by linarith
  have heLog : Real.log e.modulus ≤ H := by
    apply Real.log_le_log (by exact_mod_cast e.positive)
    have hh : (e.modulus : ℝ) ≤ Q := by exact_mod_cast he
    linarith
  have hfLog : Real.log f.modulus ≤ H := by
    apply Real.log_le_log (by exact_mod_cast f.positive)
    have hh : (f.modulus : ℝ) ≤ Q := by exact_mod_cast hf
    linarith
  let δ : ℝ := 1 / (100 * D * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity : 0 < 100 * D * H)).mpr
    have hh := mul_le_mul_of_nonneg_left hH hD.le
    dsimp [D] at *
    nlinarith
  have hRerr : δ * ((1 / 2) * Real.log e.modulus + R) ≤ 1 / 10 := by
    rw [show δ * ((1 / 2) * Real.log e.modulus + R) =
      ((1 / 2) * Real.log e.modulus + R) / (100 * D * H) by dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hrh := mul_le_mul_of_nonneg_left hH hR.le
    have hsh := mul_nonneg hS.le hHpos.le
    dsimp [D]
    nlinarith
  have hSerr : δ * (4 * (Real.log e.modulus + Real.log f.modulus) + S) ≤ 1 / 10 := by
    rw [show δ * (4 * (Real.log e.modulus + Real.log f.modulus) + S) =
      (4 * (Real.log e.modulus + Real.log f.modulus) + S) / (100 * D * H) by
        dsimp [δ]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 100 * D * H)).mpr
    have hsh := mul_le_mul_of_nonneg_left hH hS.le
    have hrh := mul_nonneg hR.le hHpos.le
    dsimp [D]
    nlinarith
  have hgap : κ / H = δ / 20 := by
    dsimp [κ, δ]
    field_simp
    ring
  apply real_zero_pair_exclusion e f δ
    ((1 / 2) * Real.log e.modulus + R)
    (4 * (Real.log e.modulus + Real.log f.modulus) + S)
    hδ hδ1 hRerr hSerr
  · change 1 - κ / H ≤ e.beta at hbe
    rwa [hgap] at hbe
  · change 1 - κ / H ≤ f.beta at hbf
    rwa [hgap] at hbf
  · simpa only [add_sub_cancel_left, add_assoc, PrimitiveRealZero.asRealCharacter] using
      hsingle e.asRealCharacter (1 + δ) (by linarith) (by linarith)
  · intro hne
    simpa only [add_sub_cancel_left, add_assoc, PrimitiveRealZero.asRealCharacter] using
      hpair e.asRealCharacter f.asRealCharacter hne (1 + δ) (by linarith) (by linarith)

end Ostmann

end OAI

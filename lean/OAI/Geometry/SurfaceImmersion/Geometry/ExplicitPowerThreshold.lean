import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! Explicit integer-power thresholds for the finitely many real powers
used by the first correction block. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

/-- The exponent of this threshold depends only on a lower bound for the
positive exponent, not on either numerical constant. -/
def powerThreshold (n : ℕ) (c b : ℝ) : ℝ := (min 1 (b/(c+1)))^n

theorem powerThreshold_spec {n : ℕ} (hn : 0 < n) {c b p : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) (hp : (n : ℝ)⁻¹ ≤ p) :
    0 < powerThreshold n c b ∧ powerThreshold n c b ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < powerThreshold n c b → c*t^p < b := by
  let q := min 1 (b/(c+1))
  have hq : 0 < q := lt_min zero_lt_one (div_pos hb (by linarith))
  have hq1 : q ≤ 1 := min_le_left _ _
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨pow_pos hq n, pow_le_one₀ hq.le hq1,?_⟩
  intro t ht hsmall
  have ht1 : t ≤ 1 := hsmall.le.trans (pow_le_one₀ hq.le hq1)
  have hroot : t^((n : ℝ)⁻¹) < q := by
    have h := Real.rpow_lt_rpow ht.le hsmall (inv_pos.mpr hn')
    change t^((n : ℝ)⁻¹) < (q^n)^((n : ℝ)⁻¹) at h
    rwa [← Real.rpow_natCast, Real.rpow_rpow_inv hq.le hn'.ne'] at h
  have htp : t^p < q :=
    (Real.rpow_le_rpow_of_exponent_ge ht ht1 hp).trans_lt hroot
  have hqb : (c+1)*q ≤ b := by
    have h := (le_div_iff₀ (show 0 < c+1 by linarith)).mp
      (show q ≤ b/(c+1) from min_le_right _ _)
    nlinarith
  calc
    c*t^p ≤ (c+1)*t^p := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht.le _)
    _ < (c+1)*q := mul_lt_mul_of_pos_left htp (by linarith)
    _ ≤ b := hqb

/-- An upper bound on the reciprocal threshold follows from upper bounds
on the coefficient and reciprocal margin. -/
lemma powerThreshold_inverse_le {n : ℕ} {c b C B : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) (hC : c ≤ C) (hB : b⁻¹ ≤ B) :
    (powerThreshold n c b)⁻¹ ≤ (1+(C+1)*B)^n := by
  have hC0 : 0 ≤ C := hc.trans hC
  have hB0 : 0 ≤ B := (inv_pos.mpr hb).le.trans hB
  have hq : 0 < min 1 (b/(c+1)) := lt_min zero_lt_one (div_pos hb (by linarith))
  have hi : (min 1 (b/(c+1)))⁻¹ ≤ 1+(C+1)*B := by
    have hh : (c+1)/b ≤ (C+1)*B := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (by linarith) hB (inv_nonneg.mpr hb.le) (by linarith)
    by_cases hle : b/(c+1) ≤ 1
    · rw [min_eq_right hle, inv_div]
      linarith
    · rw [min_eq_left (le_of_not_ge hle), inv_one]
      nlinarith
  rw [powerThreshold, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hi n

end ClosedSurfaceR4.ExactCorrection

end

end OAI

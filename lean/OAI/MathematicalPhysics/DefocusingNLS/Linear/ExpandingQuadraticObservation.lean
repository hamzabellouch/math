import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSequentialObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBallScalar

namespace OAI

/-! # Quadratic compact errors are small modulo a physical ball observation -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem expanding_quadratic_observation_estimate (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (F : Radius → FourierL2 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ L f, F L f ≤ B * ‖f‖ ^ 2)
    (hscale : ∀ L (c : ℝ) f, F L (c • f) = c ^ 2 * F L f)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hsmall : ∀ (L : Radius), (n : ℝ) ≤ L.1 → ∀ f : FourierL2,
      ‖f‖ ≤ 1 →
      (∀ y : E, ‖y‖ ≤ (n : ℝ) →
        ‖expandingTorusFunction a k L.1 f (euclideanToTorus (L.1⁻¹ • y))‖ ≤
          1 / ((n : ℝ) + 1)) → F L f ≤ ε) :
    ∀ (L : Radius), (n : ℝ) ≤ L.1 → ∀ f : FourierL2,
      F L f ≤ ε * ‖f‖ ^ 2 + B * ((n : ℝ) + 1) ^ 2 *
        ‖expandingPhysicalBall a k L.1 n ha ha1 hk L.2 f‖ ^ 2 := by
  intro L hL f
  by_cases hf : f = 0
  · subst f
    have hz : F L 0 ≤ 0 := by simpa using hbound L 0
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using
      hz.trans (show 0 ≤ B * ((n : ℝ) + 1) ^ 2 *
        ‖expandingPhysicalBall a k L.1 n ha ha1 hk L.2 0‖ ^ 2 by positivity)
  have hfp : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let s := ‖expandingPhysicalBall a k L.1 n ha ha1 hk L.2 f‖
  have hs : 0 ≤ s := norm_nonneg _
  have hnp : 0 < (n : ℝ) + 1 := by positivity
  by_cases hlocal : s ≤ ‖f‖ / ((n : ℝ) + 1)
  · let w : FourierL2 := ‖f‖⁻¹ • f
    have hwn : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfp), inv_mul_cancel₀ hfp.ne']
    have hwlocal : ∀ y : E, ‖y‖ ≤ (n : ℝ) →
        ‖expandingTorusFunction a k L.1 w (euclideanToTorus (L.1⁻¹ • y))‖ ≤
          1 / ((n : ℝ) + 1) := by
      intro y hy
      have hb := expandingPhysicalBall_point_le a k L.1 n ha ha1 hk L.2 w y hy
      have he : ‖expandingPhysicalBall a k L.1 n ha ha1 hk L.2 w‖ = ‖f‖⁻¹ * s := by
        dsimp only [w]
        rw [expandingPhysicalBall_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hfp)]
      rw [he] at hb
      apply hb.trans
      calc
        ‖f‖⁻¹ * s ≤ ‖f‖⁻¹ * (‖f‖ / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hlocal (inv_nonneg.mpr hfp.le)
        _ = 1 / ((n : ℝ) + 1) := by field_simp
    have hw := hsmall L hL w hwn.le hwlocal
    have hfw : ‖f‖ • w = f := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hfp.ne', one_smul]
    have he := hscale L ‖f‖ w
    rw [hfw] at he
    calc
      F L f = ‖f‖ ^ 2 * F L w := he
      _ ≤ ‖f‖ ^ 2 * ε := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hB (sq_nonneg ((n : ℝ) + 1))) (sq_nonneg s)]
  · have hfs : ‖f‖ ≤ ((n : ℝ) + 1) * s := by
      have ht := (div_lt_iff₀ hnp).mp (lt_of_not_ge hlocal)
      nlinarith
    have hsq : ‖f‖ ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * s ^ 2 := by
      nlinarith [sq_nonneg (((n : ℝ) + 1) * s - ‖f‖)]
    have hm := mul_le_mul_of_nonneg_left hsq hB
    calc
      F L f ≤ B * ‖f‖ ^ 2 := hbound L f
      _ ≤ B * ((n : ℝ) + 1) ^ 2 * s ^ 2 := by nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg hε.le (sq_nonneg ‖f‖)]

end DefocusingNLS

end OAI

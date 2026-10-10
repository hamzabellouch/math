import OAI.Analysis.LipschitzHilbert.Estimates.PlanarProfileBounds

namespace OAI

/-! A common finite collection of Schwartz seminorm bounds gives a
common raw-kernel constant for an entire packet family. The constant
is explicit and independent of the particular planar profile. -/

noncomputable section

namespace LipschitzHilbert

/-- The concrete general planar raw kernels and their horizontal
derivatives obey uniform product-envelope bounds whenever the profile
constant is uniformly bounded. The exact amplitude is
`(2^n*Cprof)*(M+2)*R^2`, and differentiation costs exactly `1/l`. -/
theorem uniform_planar_raw_bounds (f : SchwartzMap (ℝ × ℝ) ℂ) (n : ℕ)
    (Cprof : ℝ) (hprof : planarProfileConstant f (2 * n) ≤ Cprof)
    (a cy l W delta frequency scale R M : ℝ) (hl : 0 < l)
    (hR : 1 ≤ R) (hr : |scale / W| ≤ R) (hM : 0 ≤ M)
    (hs : |delta * l / W| ≤ 1) (hc : |frequency * delta * l| ≤ M)
    (i : Fin 3) (y x : ℝ) :
    ‖modulatedPlanarJet f a cy l W delta frequency scale y hl.ne' i x‖ ≤
      ((2 ^ n * Cprof) * (M + 2) * R ^ 2) *
        (lineEnvelope a l n x * lineEnvelope cy W n y) ∧
    ‖deriv (modulatedPlanarJet f a cy l W delta frequency scale y hl.ne' i) x‖ ≤
      (((2 ^ n * Cprof) * (M + 2) * R ^ 2) / l) *
        (lineEnvelope a l n x * lineEnvelope cy W n y) := by
  have hCprof : 0 ≤ Cprof := (planarProfileConstant_pos f (2 * n)).le.trans hprof
  let B := R ^ 2 * Cprof
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg R) hCprof
  have hcoefficient : R ^ 2 * planarProfileConstant f (2 * n) ≤ B :=
    mul_le_mul_of_nonneg_left hprof (sq_nonneg R)
  have dominate (g : ℝ × ℝ → ℂ)
      (hg : ∀ z, ‖g z‖ ≤ (R ^ 2 * planarProfileConstant f (2 * n)) *
        (lineEnvelope 0 1 (2 * n) z.1 * lineEnvelope 0 1 (2 * n) z.2)) :
      ∀ z, ‖g z‖ ≤ B *
        (lineEnvelope 0 1 (2 * n) z.1 * lineEnvelope 0 1 (2 * n) z.2) := by
    intro z
    exact (hg z).trans (mul_le_mul_of_nonneg_right hcoefficient
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have hbase := dominate _ (planar_profile_envelope f (2 * n) (scale / W) R hR hr i)
  have hdx := dominate _ (planar_profile_horizontal_envelope f (2 * n)
    (scale / W) R hR hr i)
  have hdy := dominate _ (planar_profile_vertical_envelope f (2 * n)
    (scale / W) R hR hr i)
  have hb := modulatedPlanarSlice_envelope (planarProfileJet f (scale / W) i)
    a cy l W delta frequency y B hl.ne' n hB hs hbase x
  have hd := modulatedPlanarSlice_derivative_bound (planarProfileJet f (scale / W) i)
    a cy l W delta frequency y B M hl n hB hs hc hbase hdx hdy x
  constructor
  · change ‖modulatedPlanarSlice (planarProfileJet f (scale / W) i)
        a cy l W delta frequency y hl.ne' x‖ ≤ _
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _
      (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    have hfactor : 1 ≤ M + 2 := by linarith
    calc
      2 ^ n * B ≤ (2 ^ n * B) * (M + 2) :=
        le_mul_of_one_le_right (by positivity) hfactor
      _ = (2 ^ n * Cprof) * (M + 2) * R ^ 2 := by dsimp [B]; ring
  · change ‖deriv (modulatedPlanarSlice (planarProfileJet f (scale / W) i)
        a cy l W delta frequency y hl.ne') x‖ ≤ _
    convert hd using 1
    dsimp [B]
    ring

end LipschitzHilbert

end

end OAI

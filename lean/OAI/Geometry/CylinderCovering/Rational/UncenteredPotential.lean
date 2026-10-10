import OAI.Geometry.CylinderCovering.Rational.UncenteredPotentialDefinitions
import OAI.Geometry.CylinderCovering.Rational.CoordinateDictionary

namespace OAI

noncomputable section

namespace RationalDictionary

theorem streamPotential_hasDerivAt_u (d0 u s : ℝ) :
    HasDerivAt (fun y => streamPotential d0 y s) (v2 d0 u s) u := by
  have h := ((((hasDerivAt_id u).pow 2).sub_const (c0 ^ 2 * s ^ 2)).const_mul
    (g d0 s)).div_const 2
  convert h using 1 <;> first | rfl | (simp [v2]; ring)

theorem streamPotential_hasDerivAt_s (d0 u : ℝ) {s : ℝ} (hs : s + d0 ≠ 0) :
    HasDerivAt (fun t => streamPotential d0 u t) (-v1 d0 u s) s := by
  have hpoly := (((hasDerivAt_id s).pow 2).const_mul (c0 ^ 2)).const_sub (u ^ 2)
  have h := ((hasDerivAt_g hs).mul hpoly).div_const 2
  convert h using 1 <;> first | rfl | (simp [v1]; ring)

theorem hasDerivAt_gPrime {d0 s : ℝ} (hs : s + d0 ≠ 0) :
    HasDerivAt (gPrime d0) (gSecond d0 s) s := by
  have hden := ((hasDerivAt_id s).add_const d0).pow 2
  have h := (hasDerivAt_const s (-(1 + d0))).fun_div hden (pow_ne_zero 2 hs)
  convert h using 1 <;> first | rfl |
    (simp [gSecond]; field_simp [hs]; ring)

theorem g_second_identity (d0 s : ℝ) :
    g d0 s * gSecond d0 s / 2 = gPrime d0 s ^ 2 := by
  unfold g gPrime gSecond
  by_cases hs : s + d0 = 0
  · simp [hs]
  · field_simp [hs]

theorem streamPotential_right_wall (d0 s : ℝ) :
    streamPotential d0 (c0 * s) s = 0 := by
  unfold streamPotential
  ring

theorem streamPotential_left_wall (d0 s : ℝ) :
    streamPotential d0 (-c0 * s) s = 0 := by
  unfold streamPotential
  ring

theorem uncentered_right_wall_tangent (d0 s : ℝ) :
    v1 d0 (c0 * s) s = c0 * v2 d0 (c0 * s) s := by
  unfold v1 v2
  ring

theorem uncentered_left_wall_tangent (d0 s : ℝ) :
    v1 d0 (-c0 * s) s = -c0 * v2 d0 (-c0 * s) s := by
  unfold v1 v2
  ring

theorem uncentered_right_wall_factor (d0 u s : ℝ) :
    v1 d0 u s - c0 * v2 d0 u s =
      (c0 * s - u) * (c0 * g d0 s + (c0 * s + u) * gPrime d0 s / 2) := by
  unfold v1 v2
  ring

theorem uncentered_left_wall_factor (d0 u s : ℝ) :
    v1 d0 u s + c0 * v2 d0 u s =
      (c0 * s + u) * (c0 * g d0 s + (c0 * s - u) * gPrime d0 s / 2) := by
  unfold v1 v2
  ring

theorem lineMap_right_wall (d0 k r : ℝ) (p : Plane) :
    c0 * lineMap d0 k r p 1 - lineMap d0 k r p 0 =
      (c0 * p 1 - p 0) *
        (1 - r * k * (c0 * g d0 (p 1) +
          (c0 * p 1 + p 0) * gPrime d0 (p 1) / 2)) := by
  change c0 * (p 1 + r * k * v2 d0 (p 0) (p 1)) -
    (p 0 + r * k * v1 d0 (p 0) (p 1)) = _
  have h := uncentered_right_wall_factor d0 (p 0) (p 1)
  linear_combination -(r * k) * h

theorem lineMap_left_wall (d0 k r : ℝ) (p : Plane) :
    c0 * lineMap d0 k r p 1 + lineMap d0 k r p 0 =
      (c0 * p 1 + p 0) *
        (1 + r * k * (c0 * g d0 (p 1) +
          (c0 * p 1 - p 0) * gPrime d0 (p 1) / 2)) := by
  change c0 * (p 1 + r * k * v2 d0 (p 0) (p 1)) +
    (p 0 + r * k * v1 d0 (p 0) (p 1)) = _
  have h := uncentered_left_wall_factor d0 (p 0) (p 1)
  linear_combination (r * k) * h

theorem uncentered_stream : UncenteredStreamStatement := by
  intro d0 u s hs
  exact ⟨streamPotential_hasDerivAt_u d0 u s, streamPotential_hasDerivAt_s d0 u hs,
    hasDerivAt_gPrime hs, g_second_identity d0 s,
    uncentered_right_wall_tangent d0 s, uncentered_left_wall_tangent d0 s⟩

end RationalDictionary

end

end OAI

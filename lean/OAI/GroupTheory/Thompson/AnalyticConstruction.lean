import OAI.GroupTheory.Thompson.AnalyticCurveRotation
import OAI.GroupTheory.Thompson.AnalyticCurveSeparation
import OAI.GroupTheory.Thompson.AnalyticCorrection
import OAI.GroupTheory.Thompson.AnalyticNormalization

namespace OAI

/-!
# The actual positive-displacement map on the L² unit ball

Every elementary field of the generic tube and correction constructions is
instantiated here by the explicit scalar profiles and the concrete L² curve.
The final map has no geometric or analytic certificate as a hypothesis.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

private def separationAtScale : ℝ :=
  Classical.choose (gamma_uniform_separation (1 / 32) (by norm_num))

private theorem separationAtScale_pos : 0 < separationAtScale :=
  (Classical.choose_spec (gamma_uniform_separation (1 / 32) (by norm_num))).1

private theorem separationAtScale_le (s t : ℝ) (h : (1 / 32 : ℝ) ≤ |t - s|) :
    separationAtScale ≤ ‖gamma t - gamma s‖ :=
  (Classical.choose_spec (gamma_uniform_separation (1 / 32) (by norm_num))).2 s t h

/-- The proved elementary geometry of the actual radial oscillating curve. -/
def regularCurve : RegularCurveData Hilbert where
  curve := gamma
  velocity := gammaDeriv
  tangent := u
  hasDerivAt := hasDerivAt_gamma
  norm_tangent := u_norm
  velocity_eq := gammaDeriv_eq_norm_smul_u
  speed_lower := gammaDeriv_speed_lower
  velocity_lipschitz := gammaDeriv_sub_norm_le
  tangent_lipschitz := u_sub_norm_le
  separation := separationAtScale
  separation_pos := separationAtScale_pos
  separated := separationAtScale_le

/-- The radius comes from proved uniform separation and the explicit speed bounds. -/
def tubeRadius : ℝ := regularCurve.rho

theorem tubeRadius_pos : 0 < tubeRadius := regularCurve.rho_pos

theorem tubeRadius_lt : tubeRadius < 1 / 32 := by
  have := regularCurve.rho_le
  dsimp [tubeRadius]
  linarith

/-- The literal radial, angular, and rotation inputs to the correction formula. -/
def correctionData : CorrectionData regularCurve where
  a := a
  v := v
  q := q
  R := R
  curve_eq := fun _ => rfl
  a_zero := by rw [a_of_le_two (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  a_upper := a_le_five_sixteenths
  a_late_lower := fun _ ht => a_lower_of_one_le ht.le
  q_eq := fun t => by simpa only [b, neg_div] using q_eq_b_sub_a t
  q_bound := q_abs_le
  q_lipschitz := by
    intro s t
    simpa [dist_eq_norm, Real.norm_eq_abs] using q_lipschitz.dist_le_mul t s
  norm_v := v_norm
  v_lipschitz := v_sub_norm_le
  curve_lipschitz := gamma_sub_norm_le
  norm_R := R_norm
  R_perp := R_perp
  R_lipschitz := R_sub_norm_le
  R_early := fun _ ht e => R_early_apply ht e
  tangent_early := fun _ ht => u_of_le_one ht

/-- The explicit correction, restricted to the shared actual closed unit ball. -/
def G (x : Ball) : Hilbert := correctionData.G (x : Hilbert)

theorem G_norm_lower (x : Ball) : tubeRadius / 4 ≤ ‖G x‖ :=
  correctionData.G_lower (x : Hilbert)

theorem G_outer (x : Ball) (hx : (1 / 2 : ℝ) ≤ ‖(x : Hilbert)‖) :
    G x = (x : Hilbert) := correctionData.G_outer (x : Hilbert) hx

theorem G_sub_norm_le (x y : Ball) :
    ‖G x - G y‖ ≤ correctionData.lipschitzConstant * ‖(x : Hilbert) - y‖ :=
  correctionData.G_lipschitz (x : Hilbert) (y : Hilbert)

private theorem normalizationRadius_pos : 0 < tubeRadius / 4 :=
  div_pos tubeRadius_pos (by norm_num)

/-- Negative radial normalization of the concrete nonvanishing correction. -/
def displacementMap : Ball → Ball :=
  normalizedMap G normalizationRadius_pos G_norm_lower

theorem displacementMap_norm (x : Ball) : ‖(displacementMap x : Hilbert)‖ = 1 :=
  norm_normalizedMap G normalizationRadius_pos G_norm_lower x

theorem displacementMap_displacement (x : Ball) :
    (1 / 2 : ℝ) ≤ ‖(displacementMap x : Hilbert) - x‖ :=
  normalizedMap_displacement G normalizationRadius_pos G_norm_lower G_outer x

def displacementLipschitzConstant : ℝ :=
  2 * correctionData.lipschitzConstant / (tubeRadius / 4)

theorem displacementLipschitzConstant_pos : 0 < displacementLipschitzConstant :=
  div_pos (mul_pos (by norm_num) correctionData.lipschitzConstant_pos)
    normalizationRadius_pos

theorem displacementMap_lipschitz (x y : Ball) :
    ‖(displacementMap x : Hilbert) - displacementMap y‖ ≤
      displacementLipschitzConstant * ‖(x : Hilbert) - y‖ :=
  normalizedMap_lipschitz G normalizationRadius_pos G_norm_lower G_sub_norm_le x y

/-- The unconditional analytic input used by the finite correlation proof. -/
theorem exists_displacementMap :
    ∃ (f : UnitBall Hilbert → UnitBall Hilbert) (L : ℝ),
      0 < L ∧
      (∀ x y, ‖(f x : Hilbert) - f y‖ ≤ L * ‖(x : Hilbert) - y‖) ∧
      (∀ x, (1 / 2 : ℝ) ≤ ‖(f x : Hilbert) - x‖) :=
  ⟨displacementMap, displacementLipschitzConstant, displacementLipschitzConstant_pos,
    displacementMap_lipschitz, displacementMap_displacement⟩

end ThompsonNonamenability.Analytic

end

end OAI

import OAI.GroupTheory.Thompson.TubeRegularCurve
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-!
# A quantitative lower bound for tangent projections

On a parameter interval of length at most `1 / 32`, the velocity has inner
product at least `3 / 32` with the tangent at either prescribed endpoint.
The scalar mean value theorem then bounds the projected chord from below.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace RegularCurveData

variable (C : RegularCurveData E)

theorem velocity_inner_tangent (s : ℝ) :
    inner (𝕜 := ℝ) (C.velocity s) (C.tangent s) = ‖C.velocity s‖ := by
  calc
    inner (𝕜 := ℝ) (C.velocity s) (C.tangent s) =
        inner (𝕜 := ℝ) (‖C.velocity s‖ • C.tangent s) (C.tangent s) :=
      congrArg (fun v => inner (𝕜 := ℝ) v (C.tangent s)) (C.velocity_eq s)
    _ = ‖C.velocity s‖ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, C.norm_tangent]
      simp

/-- The derivative of projection onto the fixed tangent at `s` stays positive
throughout the prescribed parameter scale. -/
theorem velocity_tangent_lower (s t : ℝ) (hst : |t - s| ≤ 1 / 32) :
    (3 / 32 : ℝ) ≤ inner (𝕜 := ℝ) (C.velocity t) (C.tangent s) := by
  have hinner := abs_real_inner_le_norm (C.velocity t - C.velocity s) (C.tangent s)
  rw [C.norm_tangent, mul_one, inner_sub_left, C.velocity_inner_tangent] at hinner
  have herror : |inner (𝕜 := ℝ) (C.velocity t) (C.tangent s) - ‖C.velocity s‖| ≤
      |t - s| := hinner.trans (C.velocity_lipschitz s t)
  have hlo := (abs_le.mp herror).1
  have hspeed := C.speed_lower s
  linarith

/-- The chord's projection onto the tangent at its first parameter controls
parameter distance. The tangent remains fixed at `s` for either order of `s`
and `t`. -/
theorem tangent_projection_lower (s t : ℝ) (hst : |t - s| ≤ 1 / 32) :
    (3 / 32 : ℝ) * |t - s| ≤
      |inner (𝕜 := ℝ) (C.curve t - C.curve s) (C.tangent s)| := by
  let f : ℝ → ℝ := fun u => inner (𝕜 := ℝ) (C.curve u) (C.tangent s)
  let f' : ℝ → ℝ := fun u => inner (𝕜 := ℝ) (C.velocity u) (C.tangent s)
  have hf : ∀ u, HasDerivAt f (f' u) u := by
    intro u
    simpa only [f, f', inner_zero_right, zero_add] using
      (C.hasDerivAt u).inner ℝ (hasDerivAt_const u (C.tangent s))
  have hfc : Continuous f :=
    continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  rw [inner_sub_left]
  change (3 / 32 : ℝ) * |t - s| ≤ |f t - f s|
  rcases lt_trichotomy s t with hlt | heq | hlt
  · obtain ⟨u, hu, hdu⟩ :=
      exists_hasDerivAt_eq_slope f f' hlt hfc.continuousOn (fun u _ => hf u)
    have hus : |u - s| ≤ 1 / 32 := by
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp hst).1, (abs_le.mp hst).2, hu.1, hu.2]
    have hlo : (3 / 32 : ℝ) ≤ f' u := C.velocity_tangent_lower s u hus
    rw [hdu] at hlo
    have hgrow : (3 / 32 : ℝ) * (t - s) ≤ f t - f s :=
      (le_div_iff₀ (sub_pos.mpr hlt)).mp hlo
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    exact hgrow.trans (le_abs_self _)
  · subst t
    simp
  · obtain ⟨u, hu, hdu⟩ :=
      exists_hasDerivAt_eq_slope f f' hlt hfc.continuousOn (fun u _ => hf u)
    have hus : |u - s| ≤ 1 / 32 := by
      apply abs_le.mpr
      constructor <;> linarith [(abs_le.mp hst).1, (abs_le.mp hst).2, hu.1, hu.2]
    have hlo : (3 / 32 : ℝ) ≤ f' u := C.velocity_tangent_lower s u hus
    rw [hdu] at hlo
    have hgrow : (3 / 32 : ℝ) * (s - t) ≤ f s - f t :=
      (le_div_iff₀ (sub_pos.mpr hlt)).mp hlo
    rw [abs_sub_comm t s, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    refine hgrow.trans ?_
    calc
      f s - f t = -(f t - f s) := (neg_sub _ _).symm
      _ ≤ |f t - f s| := neg_le_abs _

end RegularCurveData

end ThompsonNonamenability.Analytic

end

end OAI

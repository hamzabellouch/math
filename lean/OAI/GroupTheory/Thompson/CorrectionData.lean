import OAI.GroupTheory.Thompson.AnalyticTube
import OAI.GroupTheory.Thompson.AnalyticCutoffs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Elementary inputs and explicit formula for the tube correction

Every field below is a scalar, curve, or rotation identity/estimate. In
particular, no property of the corrected map is included in the inputs.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure CorrectionData (C : RegularCurveData E) where
  a : ℝ → ℝ
  v : ℝ → E
  q : ℝ → ℝ
  R : ℝ → E →L[ℝ] E
  curve_eq : ∀ t, C.curve t = a t • v t
  a_zero : a 0 = 0
  a_upper : ∀ t, a t ≤ 5 / 16
  a_late_lower : ∀ t, 1 < t → 1 / 8 ≤ a t
  q_eq : ∀ t, q t = min (a t) (-1 / 8) - a t
  q_bound : ∀ t, |q t| ≤ 7 / 16
  q_lipschitz : ∀ s t, |q t - q s| ≤ (1 / 8) * |t - s|
  norm_v : ∀ t, ‖v t‖ = 1
  v_lipschitz : ∀ s t, ‖v t - v s‖ ≤ |t - s|
  curve_lipschitz : ∀ s t, ‖C.curve t - C.curve s‖ ≤ (7 / 16) * |t - s|
  norm_R : ∀ t e, ‖R t e‖ = ‖e‖
  R_perp : ∀ t e, ⟪e, C.tangent t⟫_ℝ = 0 → ⟪R t e, v t⟫_ℝ = 0
  R_lipschitz : ∀ s t e, ‖R t e - R s e‖ ≤ 238 * |t - s| * ‖e‖
  R_early : ∀ t, t ≤ 1 → ∀ e, R t e = e
  tangent_early : ∀ t, t ≤ 1 → C.tangent t = v t

namespace CorrectionData

variable {C : RegularCurveData E} (D : CorrectionData C)

/-- The additive change on the actual, uniquely parameterized open tube. -/
def change (x : C.tube) : E :=
  (beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) • D.v (C.parameter x) +
    chi C.rho ‖C.residual x‖ • (D.R (C.parameter x) (C.residual x) - C.residual x)

/-- The actual correction inside the tube. -/
def inside (x : C.tube) : E := (x : E) + D.change x

/-- Gluing to the identity outside the open tube, including its boundary. -/
def G (x : E) : E := by
  classical
  exact if hx : x ∈ C.tube then D.inside ⟨x, hx⟩ else x

theorem G_of_mem (x : C.tube) : D.G (x : E) = D.inside x := by
  simp only [G, dite_eq_left x.property]

theorem G_of_not_mem {x : E} (hx : x ∉ C.tube) : D.G x = x := by
  simp only [G, dite_eq_right hx]

theorem inside_radial (x : C.tube) :
    D.inside x =
      (D.a (C.parameter x) + beta C.rho ‖C.residual x‖ * D.q (C.parameter x)) •
        D.v (C.parameter x) +
      ((1 - chi C.rho ‖C.residual x‖) • C.residual x +
        chi C.rho ‖C.residual x‖ • D.R (C.parameter x) (C.residual x)) := by
  have hx := C.curve_add_residual x
  rw [D.curve_eq] at hx
  unfold inside change
  rw [← hx]
  simp only [add_smul, sub_smul, one_smul, smul_sub]
  abel

include D in
theorem curve_zero : C.curve 0 = 0 := by
  rw [D.curve_eq, D.a_zero, zero_smul]

theorem norm_curve (t : ℝ) : ‖C.curve t‖ = |D.a t| := by
  rw [D.curve_eq, norm_smul, Real.norm_eq_abs, D.norm_v, mul_one]

theorem q_eq_zero {t : ℝ} (h : D.a t ≤ -1 / 8) : D.q t = 0 := by
  rw [D.q_eq, min_eq_left h, sub_self]

theorem radial_eq_min (t : ℝ) : D.a t + D.q t = min (D.a t) (-1 / 8) := by
  rw [D.q_eq]
  ring

end CorrectionData

end ThompsonNonamenability.Analytic

end

end OAI

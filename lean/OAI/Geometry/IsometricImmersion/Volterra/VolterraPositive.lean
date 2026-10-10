import OAI.Geometry.IsometricImmersion.Volterra.VolterraDifferentiation
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section
open Set
open scoped Topology

namespace SmoothLocal.ODE

theorem volterraSolution_norm_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    ‖volterraSolution r hr k‖ ≤ (1000 : ℝ) / 999 := by
  let : Nonempty (Icc (-r) r) := ⟨⟨0, ⟨by linarith, hr.le⟩⟩⟩
  let f := volterraSolution r hr k
  let T := curvatureVolterraCLM r hr k
  have hT : ‖T‖ ≤ (1 : ℝ) / 1000 := (curvatureVolterraCLM_norm_le r hr hr1 k).trans hk
  have he : f + T f = 1 := volterraSolution_equation r hr hr1 k hk
  have he' : f = 1 - T f := eq_sub_of_add_eq he
  have hn : ‖f‖ ≤ 1 + (1 : ℝ) / 1000 * ‖f‖ := by
    calc
      ‖f‖ = ‖1 - T f‖ := congrArg norm he'
      _ ≤ ‖(1 : IntervalFunctions r)‖ + ‖T f‖ := norm_sub_le _ _
      _ ≤ 1 + (1 : ℝ) / 1000 * ‖f‖ := by
        rw [norm_one]
        exact add_le_add le_rfl ((T.le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hT (norm_nonneg f)))
  change ‖f‖ ≤ (1000 : ℝ) / 999
  linarith

theorem volterraSolution_sub_one_norm_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) :
    ‖volterraSolution r hr k - 1‖ ≤ (1 : ℝ) / 999 := by
  let f := volterraSolution r hr k
  let T := curvatureVolterraCLM r hr k
  have he : f + T f = 1 := volterraSolution_equation r hr hr1 k hk
  have hsub : f - 1 = -(T f) := by
    calc
      f - 1 = (1 - T f) - 1 := congrArg (fun v => v - 1) (eq_sub_of_add_eq he)
      _ = -(T f) := by abel
  have hT : ‖T‖ ≤ (1 : ℝ) / 1000 := (curvatureVolterraCLM_norm_le r hr hr1 k).trans hk
  change ‖f - 1‖ ≤ (1 : ℝ) / 999
  rw [hsub, norm_neg]
  calc
    ‖T f‖ ≤ ‖T‖ * ‖f‖ := T.le_opNorm f
    _ ≤ ((1 : ℝ) / 1000) * (1000 / 999) := mul_le_mul hT
      (volterraSolution_norm_le r hr hr1 k hk) (norm_nonneg f) (by norm_num)
    _ = (1 : ℝ) / 999 := by norm_num

theorem volterraScalar_bounds (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (k : IntervalFunctions r) (hk : ‖k‖ ≤ (1 : ℝ) / 1000) (x : ℝ) :
    (998 : ℝ) / 999 ≤ volterraScalar r hr k x ∧
      volterraScalar r hr k x ≤ (1000 : ℝ) / 999 ∧ 0 < volterraScalar r hr k x := by
  have hn := (intervalExtension_norm_le r hr (volterraSolution r hr k - 1) x).trans
    (volterraSolution_sub_one_norm_le r hr hr1 k hk)
  change ‖volterraScalar r hr k x - 1‖ ≤ (1 : ℝ) / 999 at hn
  rw [Real.norm_eq_abs] at hn
  have hb := abs_le.mp hn
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.2]
  · linarith [hb.1]

end SmoothLocal.ODE

end

end OAI

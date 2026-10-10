import OAI.GroupTheory.Thompson.TubeNearest
import OAI.GroupTheory.Thompson.TubeComparison

namespace OAI

/-!
# The actual nearest-point parameter on a quantitative curve tube

Compact minimization, stationarity, and the tangent comparison establish
existence and uniqueness before the nearest parameter is selected.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic.RegularCurveData

open Set
open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (C : RegularCurveData E)

/-- Nearest parameters are unique throughout the metric tube. -/
theorem nearest_unique {x : E} (hx : x ∈ C.tube) {s t : ℝ}
    (hs : C.IsNearest x s) (ht : C.IsNearest x t) : s = t := by
  have hsclose : ‖x - C.curve s‖ < C.rho :=
    (C.nearest_norm_eq_infDist hs).trans_lt hx
  have htclose : ‖x - C.curve t‖ < C.rho :=
    (C.nearest_norm_eq_infDist ht).trans_lt hx
  have hxx : ‖x - x‖ < C.rho := by simpa using C.rho_pos
  have hbound := C.parameter_comparison x x s t hsclose htclose hxx
    (C.nearest_perp_tangent hs) (C.nearest_perp_tangent ht)
  have hzero : |t - s| = 0 :=
    le_antisymm (by simpa using hbound) (abs_nonneg _)
  exact (sub_eq_zero.mp (abs_eq_zero.mp hzero)).symm

/-- The unique global nearest parameter, selected after proving attainment. -/
def parameter (x : C.tube) : ℝ :=
  Classical.choose (C.nearest_exists x x.property)

theorem parameter_isNearest (x : C.tube) : C.IsNearest x (C.parameter x) :=
  (Classical.choose_spec (C.nearest_exists x x.property)).1

theorem parameter_eq_of_isNearest (x : C.tube) {t : ℝ}
    (ht : C.IsNearest x t) : C.parameter x = t :=
  C.nearest_unique x.property (C.parameter_isNearest x) ht

/-- The actual normal residual in the ambient inner-product space. -/
def residual (x : C.tube) : E := (x : E) - C.curve (C.parameter x)

theorem curve_add_residual (x : C.tube) :
    C.curve (C.parameter x) + C.residual x = (x : E) := by
  simp [residual]

theorem residual_norm (x : C.tube) :
    ‖C.residual x‖ = Metric.infDist (x : E) (range C.curve) :=
  C.nearest_norm_eq_infDist (C.parameter_isNearest x)

theorem residual_norm_lt (x : C.tube) : ‖C.residual x‖ < C.rho := by
  rw [C.residual_norm]
  exact x.property

theorem residual_perp_u (x : C.tube) :
    ⟪C.residual x, C.tangent (C.parameter x)⟫_ℝ = 0 :=
  C.nearest_perp_tangent (C.parameter_isNearest x)

theorem parameter_local_bound16 (x y : C.tube)
    (hxy : ‖(x : E) - (y : E)‖ < C.rho) :
    |C.parameter x - C.parameter y| ≤ 16 * ‖(x : E) - (y : E)‖ := by
  rw [abs_sub_comm (C.parameter x) (C.parameter y)]
  exact C.parameter_comparison x y (C.parameter x) (C.parameter y)
    (C.residual_norm_lt x) (C.residual_norm_lt y) hxy
    (C.residual_perp_u x) (C.residual_perp_u y)

theorem curve_mem_tube (t : ℝ) : C.curve t ∈ C.tube := by
  change Metric.infDist (C.curve t) (range C.curve) < C.rho
  rw [Metric.infDist_zero_of_mem (mem_range_self t)]
  exact C.rho_pos

/-- On the curve, the selected nearest parameter is the original parameter. -/
theorem parameter_curve (t : ℝ) :
    C.parameter ⟨C.curve t, C.curve_mem_tube t⟩ = t := by
  apply C.parameter_eq_of_isNearest
  intro s
  simp only [sub_self, norm_zero]
  exact norm_nonneg _

end ThompsonNonamenability.Analytic.RegularCurveData

end

end OAI

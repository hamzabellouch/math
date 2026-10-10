import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

open Set
open scoped InnerProductSpace

variable (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differential and separation data at the fixed parameter scale `1 / 32`. -/
structure RegularCurveData where
  curve : ℝ → E
  velocity : ℝ → E
  tangent : ℝ → E
  hasDerivAt : ∀ t, HasDerivAt curve (velocity t) t
  norm_tangent : ∀ t, ‖tangent t‖ = 1
  velocity_eq : ∀ t, velocity t = ‖velocity t‖ • tangent t
  speed_lower : ∀ t, (1 / 8 : ℝ) ≤ ‖velocity t‖
  velocity_lipschitz : ∀ s t, ‖velocity t - velocity s‖ ≤ |t - s|
  tangent_lipschitz : ∀ s t, ‖tangent t - tangent s‖ ≤ 16 * |t - s|
  separation : ℝ
  separation_pos : 0 < separation
  separated : ∀ s t, (1 / 32 : ℝ) ≤ |t - s| →
    separation ≤ ‖curve t - curve s‖

variable {E}

namespace RegularCurveData

variable (C : RegularCurveData E)

theorem continuous_curve : Continuous C.curve :=
  continuous_iff_continuousAt.mpr fun t => (C.hasDerivAt t).continuousAt

/-- A radius with slack in both the separation and curvature estimates. -/
def rho : ℝ := min (1 / 1024) (C.separation / 8)

theorem rho_pos : 0 < C.rho := by
  exact lt_min (by norm_num) (div_pos C.separation_pos (by norm_num))

theorem rho_le : C.rho ≤ 1 / 1024 := min_le_left _ _

theorem rho_le_separation : C.rho ≤ C.separation / 8 := min_le_right _ _

theorem four_rho_lt_separation : 4 * C.rho < C.separation := by
  have := C.rho_le_separation
  have := C.separation_pos
  linarith

theorem tangent_error_small : C.rho * 16 < 1 / 32 := by
  have := C.rho_le
  linarith

/-- The actual open metric tube around the range of the curve. -/
def tube : Set E := {x | Metric.infDist x (range C.curve) < C.rho}

theorem range_nonempty : (range C.curve).Nonempty := ⟨C.curve 0, mem_range_self 0⟩

end RegularCurveData

end ThompsonNonamenability.Analytic

end

end OAI

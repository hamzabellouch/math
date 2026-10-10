import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ChartRouting
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodizationExtendEventuallyEqFinite

namespace OAI

noncomputable section
namespace VelocityDetection.ChartRouting
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
variable (A : RoutingData)

theorem periodicPrefix_divergence (N : ℕ) (t : ℝ) (X : Coord 2) :
    divergence (periodicPrefix A N) t X = 0 := by
  apply Periodization.divergence_extend (C := 1) (contDiff_prefix A N) _
    (prefix_divergence A N)
  intro s Y hY i
  have hh := chartSet_interior (prefix_support A N s Y hY) i
  rw [abs_of_pos hh.1]
  exact hh.2.le

end VelocityDetection.ChartRouting
end

end OAI

import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Observation

namespace OAI

noncomputable section
namespace VelocityDetection.Observation
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem measurable_upperHalfPlane : MeasurableSet upperHalfPlane :=
  isOpen_lt continuous_const (continuous_apply 1) |>.measurableSet

end VelocityDetection.Observation
end

end OAI

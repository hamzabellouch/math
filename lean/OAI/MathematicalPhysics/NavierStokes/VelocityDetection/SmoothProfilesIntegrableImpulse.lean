import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfiles

namespace OAI

noncomputable section
namespace VelocityDetection.SmoothProfiles
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem integrable_impulse (p : Coord 2) (t : ℝ) : Integrable (impulse p t) :=
  (integrable_spatialPulse p).const_mul (pulse t)

end VelocityDetection.SmoothProfiles
end

end OAI

import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicSpace

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction

abbrev _root_.OAI.ContinuousMap.realLift {n : ℕ}
    (f : VelocityDetection.PeriodicSpace.compatible n) :=
  VelocityDetection.PeriodicSpace.realLift f

end

end OAI

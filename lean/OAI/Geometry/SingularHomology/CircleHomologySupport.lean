import OAI.Dynamics.EntropyCounterexample.CircleDoublingChains
import OAI.Geometry.SingularHomology.SingularSimplexCircleLift
import OAI.Geometry.SingularHomology.HomologyEvaluation
import OAI.Dynamics.EntropyCounterexample.CircleClockDoubling
import OAI.Dynamics.EntropyCounterexample.SphereSquareEquator
import OAI.Dynamics.EntropyCounterexample.CircleWindingCocycle

namespace OAI

noncomputable section

namespace Problem340.CircleHomology

theorem loopClass_ne_zero : CircleDoublingChains.loopClass ≠ 0 :=
  mt CircleDoublingChains.loopClass_eq_zero_iff.mp CircleWinding.loop_not_boundary

theorem exists_circle_doubling_eigenvector :
    ∃ v : RealSingularHomology 1 CircleDoublingChains.Circle, v ≠ 0 ∧
      realHomologyMap 1 CircleDoublingChains.doubling
        CircleDoublingChains.continuous_doubling v = (2 : ℝ) • v :=
  ⟨CircleDoublingChains.loopClass, loopClass_ne_zero,
    CircleDoublingChains.doubling_loopClass⟩

theorem exists_clock_doubling_eigenvector :
    ∃ v : RealSingularHomology 1 StandardClock, v ≠ 0 ∧
      realHomologyMap 1 CircleClockDoubling.clockDouble
        CircleClockDoubling.continuous_clockDouble v = (2 : ℝ) • v :=
  CircleClockDoubling.eigenvector_transport 1 2 CircleDoublingChains.loopClass
    loopClass_ne_zero CircleDoublingChains.doubling_loopClass

end Problem340.CircleHomology

end

end OAI

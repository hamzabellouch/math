import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakLinearMomentLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.HotWindowInput
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion

namespace OAI

/-! # Dunford–Pettis compactness for three phase-space measures -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published

theorem dunfordPettis1940Theorem321 : DunfordPettis1940Theorem321 := by
  intro T _
  constructor <;> exact l1WeakCompactnessInput _

theorem dunfordPettis1940HotWindows : DunfordPettis1940HotWindows := by
  intro A R _ _
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  unfold JetCopyDatum.AttainedCapSequence.hotWindowVolume
  exact l1WeakCompactnessInput _

theorem dunfordPettis1940HotPairWindows : DunfordPettis1940HotPairWindows := by
  intro A R _ _
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  have : SigmaFinite (volume : Measure (Velocity × Velocity)) := by
    change SigmaFinite ((volume : Measure Velocity).prod (volume : Measure Velocity))
    infer_instance
  unfold JetCopyDatum.AttainedCapSequence.hotPairWindowVolume
    JetCopyDatum.AttainedCapSequence.hotBaseWindowVolume
  exact l1WeakCompactnessInput _

end BoltzmannNonuniqueness.Published

end

end OAI

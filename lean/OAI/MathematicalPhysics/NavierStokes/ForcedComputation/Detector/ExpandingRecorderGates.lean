import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteGraph
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateMotion

namespace OAI

/-! The complete finite recorder graph drives one array of disjoint
moving gates. No selected computation is used to choose the gates. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder Set
open scoped ContDiff BigOperators

abbrev StageWire (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :=
  {ab : RecorderAddress M blank d × RecorderAddress M blank (d + 1) //
    stageEdge M hM blank d ab.1 ab.2}

theorem StageWire.source_injective (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :
    Function.Injective (fun w : StageWire M hM blank d => w.val.1) := by
  intro w z hwz
  change w.val.1 = z.val.1 at hwz
  apply Subtype.ext
  apply Prod.ext hwz
  exact stageEdge_target_unique M hM blank d
    (by rw [← hwz]; exact w.property) z.property

theorem StageWire.target_injective (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) :
    Function.Injective (fun w : StageWire M hM blank d => w.val.2) := by
  intro w z hwz
  change w.val.2 = z.val.2 at hwz
  apply Subtype.ext
  apply Prod.ext _ hwz
  exact stageEdge_source_unique M hM blank d
    (by rw [← hwz]; exact w.property) z.property

def wireCurve (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a T R R' : ℝ) (w : StageWire M hM blank d) : ℝ → Plane :=
  scheduledCenter a T (16 * R) (16 * R') w.val.1.number w.val.2.number
    (haltingControl (finiteMachine M hM) w.val.2.control)

theorem wireCurve_smooth (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a T R R' : ℝ) (w : StageWire M hM blank d) :
    ContDiff ℝ ∞ (wireCurve M hM blank d a T R R' w) :=
  scheduledCenter_smooth _ _ _ _ _ _ _

theorem wireCurve_separated (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : ℝ) {T R R' : ℝ} (hT : 0 < T) (hR : 0 < R) (hRR : R ≤ R')
    {w z : StageWire M hM blank d} (hwz : w ≠ z) (t : ℝ) :
    ∃ j, 16 * R ≤ |wireCurve M hM blank d a T R R' w t j -
      wireCurve M hM blank d a T R R' z t j| := by
  have hs : w.val.1.number ≠ z.val.1.number := fun h => hwz
    (StageWire.source_injective M hM blank d (RecorderAddress.number_injective M blank d h))
  have ht : w.val.2.number ≠ z.val.2.number := fun h => hwz
    (StageWire.target_injective M hM blank d
      (RecorderAddress.number_injective M blank (d + 1) h))
  exact scheduledCenter_separated a hT (by positivity) (by linarith) hs ht _ _ t

def recorderStageField (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a T R R' : ℝ) (t : ℝ) (x : Plane) : Plane :=
  ∑ w : StageWire M hM blank d, movingGate R (wireCurve M hM blank d a T R R' w) t x

theorem recorderStageField_smooth (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ) (a T R R' : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (recorderStageField M hM blank d a T R R')) :=
  ContDiff.sum (fun w _ => movingGate_smooth R (wireCurve_smooth M hM blank d a T R R' w))

theorem recorderStageField_tracks (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : ℝ) {T R R' : ℝ} (hT : 0 < T) (hR : 0 < R) (hRR : R ≤ R')
    (w : StageWire M hM blank d) (z : Plane) (hz : ∀ j, |z j| < 2 * R) (t : ℝ) :
    HasDerivAt (fun s => wireCurve M hM blank d a T R R' w s + z)
      (recorderStageField M hM blank d a T R R'
        t (wireCurve M hM blank d a T R R' w t + z)) t := by
  have he : recorderStageField M hM blank d a T R R' t
      (wireCurve M hM blank d a T R R' w t + z) =
      deriv (wireCurve M hM blank d a T R R' w) t := by
    apply parallelGate_plateau hR
      (fun w => wireCurve M hM blank d a T R R' w t)
      (fun w => deriv (wireCurve M hM blank d a T R R' w) t) w
    · intro j
      simpa only [Pi.add_apply, add_sub_cancel_left] using hz j
    · intro q hqw
      exact wireCurve_separated M hM blank d a hT hR hRR (Ne.symm hqw) t
  rw [he]
  exact ((wireCurve_smooth M hM blank d a T R R' w).differentiable (by simp) t).hasDerivAt.add_const z

end ForcedComputation.ExpandingDetector

end

end OAI

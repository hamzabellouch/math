import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderGates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateCollars

namespace OAI

/-! Time collars, incompressibility and rigid motion for the entire finite
recorder array. The array includes every defined address transition. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder Set MeasureTheory
open scoped BigOperators

theorem recorderStageField_zero_before (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : ℝ) {T R R' : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ≤ a) (x : Plane) :
    recorderStageField M hM blank d a T R R' t x = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  exact scheduledGate_zero_before R a hT (16 * R) (16 * R')
    w.val.1.number w.val.2.number (haltingControl (finiteMachine M hM) w.val.2.control) ht x

theorem recorderStageField_zero_after (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : ℝ) {T R R' : ℝ} (hT : 0 < T) {t : ℝ} (ht : a + T ≤ t) (x : Plane) :
    recorderStageField M hM blank d a T R R' t x = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  exact scheduledGate_zero_after R a hT (16 * R) (16 * R')
    w.val.1.number w.val.2.number (haltingControl (finiteMachine M hM) w.val.2.control) ht x

theorem recorderStageField_properties (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a T : ℝ) {R : ℝ} (hR : 0 < R) (R' t : ℝ) :
    HasCompactSupport (recorderStageField M hM blank d a T R R' t) ∧
      (∀ x, PlanarHamiltonian.divergence (recorderStageField M hM blank d a T R R' t) x = 0) ∧
      (∫ x, recorderStageField M hM blank d a T R R' t x) = 0 :=
  parallelGate_properties hR
    (fun w : StageWire M hM blank d => wireCurve M hM blank d a T R R' w t)
    (fun w : StageWire M hM blank d => deriv (wireCurve M hM blank d a T R R' w) t)

theorem recorderStageField_rigid (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : ℝ) {T R R' : ℝ} (hT : 0 < T) (hR : 0 < R) (hRR : R ≤ R')
    (w : StageWire M hM blank d) (t : ℝ) (x : Plane)
    (hx : ∀ j, |x j - wireCurve M hM blank d a T R R' w t j| < 2 * R) :
    recorderStageField M hM blank d a T R R' t x =
      deriv (wireCurve M hM blank d a T R R' w) t := by
  apply parallelGate_plateau hR
    (fun w => wireCurve M hM blank d a T R R' w t)
    (fun w => deriv (wireCurve M hM blank d a T R R' w) t) w x hx
  intro q hqw
  exact wireCurve_separated M hM blank d a hT hR hRR (Ne.symm hqw) t

end ForcedComputation.ExpandingDetector

end

end OAI

import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ArrayScalars
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MildScalarContDiffScalar
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfilesLocalSupportImpulse

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks TailSpace SmoothProfiles
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

def driftData (hν : 0 < ν) (i : Fin 2) : MildScalar.SupportedData :=
  ⟨fun t X => field hb table terminal ν m t X i,
    (contDiff_apply ℝ ℝ i).comp (contDiff_field hb table terminal ν m hν),
    localSupport_field hb table terminal ν m hν i⟩

@[simp] theorem driftData_scalar (hν : 0 < ν) (i : Fin 2) (t : ℝ) (X : Coord 2) :
    (driftData hb table terminal ν m hν i).scalar t X = field hb table terminal ν m t X i := rfl

def scalarSolution (hν : 0 < ν) (p : Coord 2) : ScalarField 2 :=
  MildScalar.scalar hν (driftData hb table terminal ν m hν) (impulseData p)

theorem contDiff_scalarSolution (hν : 0 < ν) (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (scalarSolution hb table terminal ν m hν p)) :=
  MildScalar.contDiff_scalar hν _ _ (impulseData_nonpos p)

theorem scalarSolution_C1Tails (hν : 0 < ν) (p : Coord 2) :
    C1Tails (scalarSolution hb table terminal ν m hν p) :=
  MildScalar.scalar_C1Tails hν _ _

theorem scalarSolution_D_Tails (hν : 0 < ν) (p : Coord 2) (i : Fin 2) :
    ContinuousTails (spatialD i (scalarSolution hb table terminal ν m hν p)) :=
  MildScalar.scalar_D_Tails hν _ _ i

theorem scalarSolution_DD_Tails (hν : 0 < ν) (p : Coord 2) (i j : Fin 2) :
    ContinuousTails (spatialD j (spatialD i (scalarSolution hb table terminal ν m hν p))) :=
  MildScalar.scalar_DD_Tails hν _ _ i j

theorem scalarSolution_equation (hν : 0 < ν) (p : Coord 2) {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    timeD (scalarSolution hb table terminal ν m hν p) t X +
      advection (field hb table terminal ν m) (scalarSolution hb table terminal ν m hν p) t X =
        ν * laplacian (scalarSolution hb table terminal ν m hν p) t X + impulse p t X := by
  exact MildScalar.scalar_equation hν (driftData hb table terminal ν m hν) (impulseData p)
    (fun t _ X => divergence_field hb table terminal ν m hν t X) ht X

@[simp] theorem scalarSolution_zero (hν : 0 < ν) (p X : Coord 2) :
    scalarSolution hb table terminal ν m hν p 0 X = 0 :=
  MildScalar.scalar_zero hν _ _ X

theorem scalarSolution_properties (hν : 0 < ν) (p : Coord 2) :
    (∀ t ≥ 0, ∀ X, 0 ≤ scalarSolution hb table terminal ν m hν p t X) ∧
    (∀ t, Integrable (scalarSolution hb table terminal ν m hν p t)) ∧
    (∀ t ≥ 0, (∫ X, scalarSolution hb table terminal ν m hν p t X) = step t) :=
  scalar_properties_of_C1Tails hb table terminal ν m hν p
    (contDiff_scalarSolution hb table terminal ν m hν p)
    (scalarSolution_C1Tails hb table terminal ν m hν p)
    (scalarSolution_D_Tails hb table terminal ν m hν p)
    (scalarSolution_DD_Tails hb table terminal ν m hν p)
    (fun _ ht => scalarSolution_equation hb table terminal ν m hν p ht)
    (scalarSolution_zero hb table terminal ν m hν p)

def velocity (hν : 0 < ν) (p : Coord 2) : VectorField 3 :=
  liftVelocity (field hb table terminal ν m) (scalarSolution hb table terminal ν m hν p)

theorem contDiff_velocity (hν : 0 < ν) (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (velocity hb table terminal ν m hν p)) := by
  convert JointCalculus.contDiff_lift (contDiff_field hb table terminal ν m hν)
    (contDiff_scalarSolution hb table terminal ν m hν p) using 1
  funext q
  simp only [uncurry, velocity, liftVelocity, JointCalculus.lift, JointCalculus.projection_apply]

theorem velocity_comparisonClass (hν : 0 < ν) (p : Coord 2) :
    Cylinder.ComparisonClass
      (fun t x => velocity hb table terminal ν m hν p t (Cylinder.join x)) (fun _ _ => 0) :=
  comparisonClass_of_scalar_tails hb table terminal ν m hν
    (contDiff_scalarSolution hb table terminal ν m hν p)
    (scalarSolution_C1Tails hb table terminal ν m hν p)
    (scalarSolution_D_Tails hb table terminal ν m hν p)
    (scalarSolution_DD_Tails hb table terminal ν m hν p)

theorem velocity_NavierStokes (hν : 0 < ν) (p : Coord 2) :
    NavierStokes ν (velocity hb table terminal ν m hν p) (fun _ _ => 0)
      (force hb table terminal ν m p) :=
  force_NavierStokes hb table terminal ν m hν p _
    (fun _ ht => scalarSolution_equation hb table terminal ν m hν p ht)
    (scalarSolution_zero hb table terminal ν m hν p)

theorem velocity_unique (hν : 0 < ν) (p : Coord 2) {v : VectorField 3} {q : ScalarField 3}
    (hv : Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
      (fun t x => q t (Cylinder.join x)))
    (hNS : NavierStokes ν v q (force hb table terminal ν m p)) :
    ∀ t ≥ 0, (∀ x, v t x = velocity hb table terminal ν m hν p t x) ∧ (∀ x, q t x = 0) :=
  Cylinder.comparison_unique_coordinates hν.le
    (velocity_comparisonClass hb table terminal ν m hν p) hv
    (velocity_NavierStokes hb table terminal ν m hν p) hNS

theorem velocity_detection (hν : 0 < ν) (c₀ : Configuration (Fin N))
    (hm : 1 ≤ m) (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0)
    (hdir : IncomingDirection table) (hin : IncomingRule table)
    (hterm : NoOutgoing table terminal) (hcont : Continues hb table terminal c₀)
    (hinit : c₀.state ≠ terminal) :
    Observation.planeEvent
      (velocity hb table terminal ν m hν (point hb table terminal ν m c₀ 0)) ↔
        Reaches hb table terminal c₀ :=
  detection_of_C1Tails hb table terminal ν m hν c₀
    (contDiff_scalarSolution hb table terminal ν m hν _)
    (scalarSolution_C1Tails hb table terminal ν m hν _)
    (scalarSolution_D_Tails hb table terminal ν m hν _)
    (scalarSolution_DD_Tails hb table terminal ν m hν _)
    (fun _ ht => scalarSolution_equation hb table terminal ν m hν _ ht)
    (scalarSolution_zero hb table terminal ν m hν _) hm hc₀ hdir hin hterm hcont hinit

end VelocityDetection.ExpandingArray
end

end OAI

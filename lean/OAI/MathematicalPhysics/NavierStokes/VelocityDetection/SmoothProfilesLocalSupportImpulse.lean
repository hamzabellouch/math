import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SmoothProfiles
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.MildScalarSupportedData

namespace OAI

noncomputable section
namespace VelocityDetection.SmoothProfiles
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem localSupport_impulse (p : Coord 2) : TailSpace.LocalHorizontalSupport (impulse p) := by
  intro T hT
  refine ⟨Prod.snd '' tsupport (uncurry (impulse p)),
    (compactSupport_impulse p).image continuous_snd, ?_⟩
  intro t _ X hX
  change uncurry (impulse p) (t,X) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact hX ⟨(t,X),hp,rfl⟩

def impulseData (p : Coord 2) : MildScalar.SupportedData :=
  ⟨impulse p, contDiff_impulse p, localSupport_impulse p⟩

@[simp] theorem impulseData_scalar (p : Coord 2) : (impulseData p).scalar = impulse p := rfl

theorem impulseData_nonpos (p : Coord 2) (t : ℝ) (ht : t ≤ 0) (X : Coord 2) :
    (impulseData p).scalar t X = 0 :=
  congrFun (impulse_zero_of_time_nonpos p ht) X

end VelocityDetection.SmoothProfiles
end

end OAI

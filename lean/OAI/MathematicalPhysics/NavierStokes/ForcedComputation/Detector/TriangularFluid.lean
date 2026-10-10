import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularLift
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarGlobalExistence
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.AutonomousStartup

namespace OAI

/-! A prescribed planar drift and scalar source determine the full external
force before the transported scalar is solved. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

def triangularVelocity (a : ℝ → Plane → Plane) (w : ℝ → Plane → ℝ) : Velocity :=
  fun y => triangularLift (a y.1) (w y.1) y.2

def planarResidual (ν : ℝ) (a : ℝ → Plane → Plane) (t : ℝ) (x : Plane) : Plane :=
  deriv (fun s => a s x) t + fderiv ℝ (a t) x (a t x) -
    ν • planarVectorLaplacian (a t) x

def triangularForce (ν : ℝ) (a : ℝ → Plane → Plane) (h : ℝ → Plane → ℝ) : Velocity :=
  fun y => triangularLift (planarResidual ν a y.1) (h y.1) y.2

theorem triangularVelocity_smooth {a : ℝ → Plane → Plane} {w : ℝ → Plane → ℝ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) :
    ContDiff ℝ ∞ (triangularVelocity a w) := by
  have hz : ContDiff ℝ ∞ (fun y : SpaceTime => (y.1, horizontalLinear y.2)) :=
    contDiff_fst.prodMk (horizontalLinear.contDiff.comp contDiff_snd)
  exact (planeInclusion.contDiff.comp (ha.comp hz)).add
    ((hw.comp hz).smul contDiff_const)

theorem triangularVelocity_timeDerivative {a : ℝ → Plane → Plane}
    {w : ℝ → Plane → ℝ} (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) (t : ℝ) (x : Space) :
    timeDerivative (triangularVelocity a w) t x =
      triangularLift (fun z => deriv (fun s => a s z) t)
        (fun z => deriv (fun s => w s z) t) x := by
  have ha' : HasDerivAt (fun s => a s (horizontalLinear x))
      (deriv (fun s => a s (horizontalLinear x)) t) t :=
    ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) t).hasDerivAt
  have hw' : HasDerivAt (fun s => w s (horizontalLinear x))
      (deriv (fun s => w s (horizontalLinear x)) t) t :=
    ((hw.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) t).hasDerivAt
  exact ((planeInclusion.hasFDerivAt.comp_hasDerivAt t ha').add
    (hw'.smul_const (basis 2))).deriv

theorem triangularVelocity_periodic {a : ℝ → Plane → Plane} {w : ℝ → Plane → ℝ}
    (ha : ∀ t, PlanePeriodic (a t)) (hw : ∀ t, PlanePeriodic (w t)) :
    SpatiallyPeriodic 1 (triangularVelocity a w) := by
  intro t x n
  have he : horizontalLinear (x + latticeVector 1 n) =
      horizontalLinear x + fun j => (n j.castSucc : ℝ) := by
    ext j
    fin_cases j <;> simp [horizontalLinear, latticeVector]
  simp only [triangularVelocity, triangularLift, he]
  rw [ha t (horizontalLinear x) (fun j => n j.castSucc),
    hw t (horizontalLinear x) (fun j => n j.castSucc)]

theorem GlobalTorusScalarSolution.deriv_eq {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hs : GlobalTorusScalarSolution ν a h w w₀)
    (hw : ContDiff ℝ ∞ (Function.uncurry w)) {t : ℝ} (ht : 0 ≤ t) (x : Plane) :
    deriv (fun s => w s x) t = scalarGenerator ν (a t) (w t) x + h t x := by
  have htI : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hdiff : DifferentiableAt ℝ (fun s => w s x) t :=
    (hw.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t
  have hu := uniqueDiffOn_Icc (by linarith : (0 : ℝ) < t + 1) t htI
  rw [← hdiff.derivWithin hu]
  exact ((hs (t + 1) (by linarith)).equation t htI x).derivWithin hu

theorem triangularVelocity_residual {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hs : GlobalTorusScalarSolution ν a h w w₀) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    residual ν (triangularVelocity a w) (t, x) = triangularForce ν a h (t, x) := by
  have has : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hws : ContDiff ℝ ∞ (w t) := hw.comp (contDiff_const.prodMk contDiff_id)
  unfold residual
  rw [triangularVelocity_timeDerivative ha hw,
    show (fun y => triangularVelocity a w (t, y)) = triangularLift (a t) (w t) from rfl,
    triangularLift_advection has hws, triangularLift_laplacian has hws]
  simp only [triangularLift, triangularForce, planarResidual,
    map_add, map_sub, map_smul, smul_add, smul_smul]
  rw [hs.deriv_eq hw ht]
  unfold scalarGenerator
  module

theorem triangularVelocity_solution {ν : ℝ} {a : ℝ → Plane → Plane}
    {h w : ℝ → Plane → ℝ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hs : GlobalTorusScalarSolution ν a h w (fun _ => 0))
    (hpa : ∀ t, PlanePeriodic (a t)) (hpw : ∀ t, PlanePeriodic (w t))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    (ha₀ : ∀ x, a 0 x = 0) :
    IsClassicalSolution 1 ν (triangularForce ν a h) (triangularVelocity a w) (fun _ => 0) := by
  have hU := triangularVelocity_smooth ha hw
  have hsol := residual_solves_NS hU (triangularVelocity_periodic hpa hpw)
    (fun t x => by
      rw [show (fun y => triangularVelocity a w (t, y)) = triangularLift (a t) (w t) from rfl,
        triangularLift_divergence (a := a t) (w := w t) (ha.comp (contDiff_const.prodMk contDiff_id))
          (hw.comp (contDiff_const.prodMk contDiff_id)), hdiv])
    (fun x => by
      have hw₀ := congrFun (hs 0 le_rfl).initial (horizontalLinear x)
      simp [triangularVelocity, triangularLift, ha₀, hw₀]) ν
  refine { hsol with equation := ?_ }
  intro t ht x
  rw [← triangularVelocity_residual ha hw hs ht x]
  exact hsol.equation t ht x

end ForcedComputation.VelocityDetector

end

end OAI

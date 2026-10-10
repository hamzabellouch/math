import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.JointCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty

theorem timeD_eq_deriv {f : ScalarField 2} {t : ℝ} (ht : 0 ≤ t) (X : Coord 2)
    (hf : DifferentiableAt ℝ (uncurry f) (t, X)) :
    timeD f t X = deriv (fun s => f s X) t := by
  exact (hf.comp t (differentiableAt_id.prodMk (differentiableAt_const X))).derivWithin
    (uniqueDiffOn_Ici 0 t ht)

end VelocityDetection.JointCalculus
end

end OAI

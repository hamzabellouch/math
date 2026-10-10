import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatEvolution

namespace OAI

/-! Supremum-norm stability of the explicit periodic heat evolution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

theorem torusHeatEvolution_stability (hK : TorusHeatInput) {g h : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgp : PlanePeriodic g) (hhp : PlanePeriodic h)
    {E : ℝ} (hE : ∀ x, |g x - h x| ≤ E) {t : ℝ} (ht : 0 ≤ t) (x : Plane) :
    |torusHeatEvolution g t x - torusHeatEvolution h t x| ≤ E := by
  have he : (fun y => h y + (g y - h y)) = g := by
    funext y
    ring
  have hadd := torusHeatEvolution_add hK hh.continuous (hg.sub hh).continuous t x
  rw [he] at hadd
  rw [hadd, add_sub_cancel_left]
  exact torusHeatEvolution_error_bound hK (hg.sub hh)
    (fun y k => by dsimp only; rw [hgp y k, hhp y k]) hE ht x

end ForcedComputation.VelocityDetector

end

end OAI

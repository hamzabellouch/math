import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedFluid

namespace OAI

/-! The flat-coordinate force depends only on a germ. No smoothness away
from the point is needed for this locality statement. -/

noncomputable section
open Filter
open scoped Topology
open ShearFlows

namespace ForcedComputation

theorem force_congr_germ {U V : Velocity} {t : ℝ} {x : Space}
    (he : U =ᶠ[𝓝 (t, x)] V) (ν : ℝ) : force ν U (t, x) = force ν V (t, x) := by
  have ht : (fun s => U (s, x)) =ᶠ[𝓝 t] fun s => V (s, x) :=
    he.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hx : (fun z => U (t, z)) =ᶠ[𝓝 x] fun z => V (t, z) :=
    he.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hd (j : Fin 3) : derivative (fun z => U (t, z)) j =ᶠ[𝓝 x]
      derivative (fun z => V (t, z)) j :=
    (hx.fderiv (𝕜 := ℝ)).mono (fun z hz => congrArg (fun A => A (basis j)) hz)
  have hl : laplacian (fun z => U (t, z)) x = laplacian (fun z => V (t, z)) x := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun A => A (basis j)) ((hd j).fderiv_eq (𝕜 := ℝ))
  change deriv (fun s => U (s, x)) t - ν • laplacian (fun z => U (t, z)) x =
    deriv (fun s => V (s, x)) t - ν • laplacian (fun z => V (t, z)) x
  rw [ht.deriv_eq, hl]

end ForcedComputation

end

end OAI

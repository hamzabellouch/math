import Mathlib
import OAI.Geometry.WeakMTW.Potentials.PotentialGraphGlobal

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]

 theorem cost_coords_smooth {x y : M}
     (h : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun q : M×M => cost q.1 q.2) (x,y)) :
     ContDiffAt ℝ ∞ (fun q : Model n×Model n =>
       cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm q.2))
       (chartAt (Model n) x x,chartAt (Model n) y y) := by
   let c := chartAt (Model n) x
   let d := chartAt (Model n) y
   have hx : c x ∈ c.target := c.map_source (mem_chart_source (Model n) x)
   have hy : d y ∈ d.target := d.map_source (mem_chart_source (Model n) y)
   have hc : ContMDiffAt 𝓘(ℝ,Model n) (model n) ∞ c.symm (c x) :=
     contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hx)
   have hd : ContMDiffAt 𝓘(ℝ,Model n) (model n) ∞ d.symm (d y) :=
     contMDiffOn_chart_symm.contMDiffAt (d.open_target.mem_nhds hy)
   have hp : ContMDiffAt 𝓘(ℝ,Model n×Model n) ((model n).prod (model n)) ∞
       (fun q : Model n×Model n => (c.symm q.1,d.symm q.2)) (c x,d y) :=
     (hc.comp (c x,d y) (contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst)).prodMk
       (hd.comp (c x,d y) (contMDiffAt_iff_contDiffAt.mpr contDiffAt_snd))
   have h' : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
       (fun q : M×M => cost q.1 q.2) (c.symm (c x),d.symm (d y)) := by
     simpa only [c.left_inv (mem_chart_source (Model n) x),d.left_inv (mem_chart_source (Model n) y)] using h
   exact contMDiffAt_iff_contDiffAt.mp (ContMDiffAt.comp (f := fun q : Model n×Model n => (c.symm q.1,d.symm q.2))
     (g := fun q : M×M => cost q.1 q.2) (c x,d y) h' hp)

variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

  noncomputable def potentialHomeomorph (hMTW : HasWeakMTW (n := n) (M := M))
     {u : M → ℝ} (hu : IsPotential u) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
     potentialGraph (n := n) u ≃ₜ M :=
   IsHomeomorph.homeomorph (potentialProjection u t)
     (((globalSupportingProperty hMTW hu).2 t ht ht1).1)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

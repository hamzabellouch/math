import OAI.Geometry.SurfaceImmersion.Geometry.TransverseReflection

namespace OAI

/-! The transverse orientation of the next time chart can always be
chosen to give a positive derivative at the attachment point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

namespace SurfaceTimeChart

theorem positive_transition (c d : SurfaceTimeChart F) (x : M)
    (hxc : x ∈ c.coord.source) (hxd : x ∈ d.coord.source) :
    ∃ e : SurfaceTimeChart F, e.coord.source = d.coord.source ∧
      (∀ y t, d.coord y = ![0,t] → e.coord y = ![0,t]) ∧
      0 < fderiv ℝ (e.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0 := by
  have hn := (time_coordinate_transition c.coord d.coord c.smooth c.inverse_smooth
    d.smooth d.inverse_smooth c.time d.time hxc hxd).2.2
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hci := c.inverse_smooth.contMDiffAt
      (c.coord.open_target.mem_nhds (c.coord.map_source hxc))
    have hds : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d.coord (c.coord.symm (c.coord x)) :=
      (c.coord.left_inv hxc).symm ▸ d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hxd)
    have hd : DifferentiableAt ℝ (d.coord ∘ c.coord.symm) (c.coord x) :=
      (hds.comp (c.coord x) hci).contDiffAt.differentiableAt (by simp)
    refine ⟨d.reflect,rfl,fun y t h => d.reflect_axis h,?_⟩
    rw [reflect_transition c d x hd]
    change 0 < -(fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0)
    exact neg_pos.mpr hneg
  · exact ⟨d,rfl,fun _ _ h => h,hpos⟩

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

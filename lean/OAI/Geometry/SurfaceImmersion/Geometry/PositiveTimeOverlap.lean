import OAI.Geometry.SurfaceImmersion.Geometry.OrientedTimeTransition

namespace OAI

/-! Positivity of the actual transverse transition persists on an open
surface neighborhood of the chosen attachment point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}
namespace SurfaceTimeChart

theorem positive_overlap (c d : SurfaceTimeChart F) (x : M)
    (hxc : x ∈ c.coord.source) (hxd : x ∈ d.coord.source)
    (hpos : 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ c.coord.source ∩ d.coord.source ∧
      ∀ y ∈ U, 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord y) ![1,0] 0 := by
  have hc := c.inverse_smooth.contMDiffAt
    (c.coord.open_target.mem_nhds (c.coord.map_source hxc))
  have hd : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d.coord (c.coord.symm (c.coord x)) :=
    (c.coord.left_inv hxc).symm ▸ d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hxd)
  have hD := (hd.comp (c.coord x) hc).contDiffAt.continuousAt_fderiv (by simp)
  have hv : ContinuousAt (fun z : Base => fderiv ℝ (d.coord ∘ c.coord.symm) z (![1,0] : Base) 0)
      (c.coord x) := (continuous_apply (0:Fin 2)).continuousAt.comp
        (hD.clm_apply continuousAt_const)
  have hvalue : ∀ᶠ y in 𝓝 x, 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord y) ![1,0] 0 :=
    (hv.comp (c.coord.continuousAt hxc)).eventually (isOpen_Ioi.mem_nhds hpos)
  have hall : ∀ᶠ y in 𝓝 x, y ∈ c.coord.source ∧ y ∈ d.coord.source ∧
      0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord y) ![1,0] 0 := by
    filter_upwards [c.coord.open_source.mem_nhds hxc,d.coord.open_source.mem_nhds hxd,hvalue] with y hyc hyd hy
    exact ⟨hyc,hyd,hy⟩
  obtain ⟨U,hU,hUopen,hxU⟩ := eventually_nhds_iff.mp hall
  exact ⟨U,hUopen,hxU,fun y hy => ⟨(hU y hy).1,(hU y hy).2.1⟩,
    fun y hy => (hU y hy).2.2⟩

end SurfaceTimeChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartTransition

namespace OAI

/-! A later curve's transverse coordinate vector, transported to the
current phase chart and extended smoothly from its compact overlap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma fderiv_local_inverse_injective
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {x : Base} (hx : x ∈ e.source) : Function.Injective (fderiv ℝ e x) := by
  have hd := ((he x hx).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hdi := ((hi (e x) (e.map_source hx)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
  have heq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hc : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp x hdi hd,heq.fderiv_eq,fderiv_id]
  intro v w h
  have hh := congrArg (fderiv ℝ e.symm (e x)) h
  change ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) v =
    ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) w at hh
  simpa only [hc,ContinuousLinearMap.id_apply] using hh

theorem compact_transverse_vector
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.target) :
    ∃ v : Base → Base, ContDiff ℝ ∞ v ∧
      ∀ x ∈ K, v x = fderiv ℝ e (e.symm x) dy ∧ v x ≠ 0 := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    he.fderiv_of_isOpen e.open_source (by simp)
  have hvec : ContDiffOn ℝ ∞ (fun x => fderiv ℝ e (e.symm x) dy) e.target :=
    (hD.clm_apply contDiffOn_const).comp hi e.symm.mapsTo
  obtain ⟨U,_,hKU,_,v,hv,hveq⟩ := CollarVelocity.compact_smooth_extension hK e.open_target hKe hvec
  refine ⟨v,hv,?_⟩
  intro x hx
  have hh := hveq (hKU hx)
  refine ⟨hh,?_⟩
  rw [hh]
  have hinj := fderiv_local_inverse_injective e he hi (e.map_target (hKe hx))
  intro hz
  have hdy := hinj (hz.trans (map_zero (fderiv ℝ e (e.symm x))).symm)
  exact (show (dy : Base) ≠ 0 from by simp [dy]) hdy

end ClosedSurfaceR4.PhaseGeometry

end

end OAI

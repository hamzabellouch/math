import OAI.Geometry.SurfaceImmersion.Geometry.NormalFormDirectionRegularity
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapCoordinateStrip

namespace OAI

/-! Retain the actual smooth coordinate change from a strip chart to
an endpoint's standard crosscap chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_chart_transition (C : SurfaceCrosscapCoordinates f p)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (hp : p ∈ c.source) {φ : Base → ProjectionTarget 3}
    (hφ : φ =ᶠ[𝓝 (c p)] f ∘ c.symm) :
    ∃ g : Base → Base, ContDiff ℝ ∞ g ∧ g (c p) = 0 ∧
      Function.Bijective (fderiv ℝ g (c p)) ∧
      φ =ᶠ[𝓝 (c p)] C.target ∘ (standardCrosscap ∘ g) := by
  let V := c.target ∩ c.symm ⁻¹' C.source.source
  have hV : IsOpen V := c.symm.isOpen_inter_preimage C.source.open_source
  have hpV : c p ∈ V := by
    refine ⟨c.map_source hp,?_⟩
    change c.symm (c p) ∈ C.source.source
    rw [c.left_inv hp]
    exact C.source_mem
  have hlocal : ContDiffOn ℝ ∞ (C.source ∘ c.symm) V :=
    (C.source_smooth.comp (hci.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  obtain ⟨U,hU,h0U,hUV,g,hg,hEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := c p)) hV (singleton_subset_iff.mpr hpV) hlocal
  have hpU : c p ∈ U := h0U (mem_singleton _)
  have hEqg := hEq.eventuallyEq_of_mem (hU.mem_nhds hpU)
  have hg0 : g (c p) = 0 := by
    rw [hEqg.eq_of_nhds]
    change C.source (c.symm (c p)) = 0
    rw [c.left_inv hp,C.source_center]
  have hDc : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hDC : C.source.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨C.source_smooth.mdifferentiableOn (by simp),C.source_inverse_smooth.mdifferentiableOn (by simp)⟩
  have hgD : Function.Bijective (fderiv ℝ g (c p)) := by
    rw [hEqg.fderiv_eq,← mfderiv_eq_fderiv,mfderiv_comp (c p)
      (hDC.mdifferentiableAt hpV.2) (hDc.mdifferentiableAt hpV.1)]
    exact (hDC.mfderiv_bijective hpV.2).comp (hDc.mfderiv_bijective hpV.1)
  refine ⟨g,hg,hg0,hgD,?_⟩
  filter_upwards [hφ,hEqg,hV.mem_nhds hpV] with x hφx hgx hx
  change φ x = C.target (standardCrosscap (g x))
  calc
    φ x = f (c.symm x) := hφx
    _ = C.target (standardCrosscap (C.source (c.symm x))) := C.model_eq _ hx.2
    _ = C.target (standardCrosscap (g x)) := by rw [hgx]; rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

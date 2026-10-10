import OAI.Geometry.SurfaceImmersion.Atlas.AxisParameterCoordinates

namespace OAI

/-! Actual smooth source coordinates at a crosscap which agree exactly
with the chosen source-arc parameter, retaining the full map formula. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_arc_coordinates (c : SurfaceCrosscapCoordinates f p)
    {γ : ℝ → M} {a : ℝ} (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (he0 : e a = 0)
    (hγ : γ =ᶠ[𝓝 a] c.axisCurve ∘ e) :
    ∃ d : OpenPartialHomeomorph M Base,
      d.source = c.source.source ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target ∧
      (∀ᶠ t in 𝓝 a, γ t ∈ d.source ∧ d (γ t) = crosscapAxis t) ∧
      ∀ x ∈ d.source, f x = c.target (standardCrosscap ![(d x) 0,e ((d x) 1)]) := by
  let H := axisParameterCoordinates e
  let d := c.source.transHomeomorph H
  have hds : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source :=
    (axisParameterCoordinates_smooth hei).contMDiff.comp_contMDiffOn c.source_smooth
  have hdi : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target := by
    apply c.source_inverse_smooth.comp
      (axisParameterCoordinates_inverse_smooth hes).contMDiff.contMDiffOn
    intro x hx
    exact hx
  have haxis0 : crosscapAxis (e a) ∈ c.source.target := by
    rw [he0,map_zero,← c.source_center]
    exact c.source.map_source c.source_mem
  have hnear : ∀ᶠ t in 𝓝 a, crosscapAxis (e t) ∈ c.source.target :=
    (crosscapAxis.continuous.comp e.continuous).continuousAt.eventually (c.source.open_target.mem_nhds haxis0)
  refine ⟨d,rfl,hds,hdi,?_,?_⟩
  · filter_upwards [hγ,hnear] with t ht htS
    refine ⟨?_,?_⟩
    · change γ t ∈ c.source.source
      rw [ht]
      exact c.source.map_target htS
    · change H (c.source (γ t)) = crosscapAxis t
      rw [ht]
      change H (c.source (c.source.symm (crosscapAxis (e t)))) = crosscapAxis t
      rw [c.source.right_inv htS]
      exact axisParameterCoordinates_axis e t
  · intro x hx
    have hrecover : ![(d x) 0,e ((d x) 1)] = c.source x := by
      exact H.symm_apply_apply (c.source x)
    rw [hrecover]
    exact c.model_eq x hx

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

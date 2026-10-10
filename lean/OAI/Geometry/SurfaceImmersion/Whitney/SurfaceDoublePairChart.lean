import OAI.Geometry.SurfaceImmersion.Atlas.ZeroSliceLineChart
import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairLocalRegularization
import OAI.Geometry.SurfaceImmersion.Whitney.CompactDoublePairs

namespace OAI

/-! Every transverse distinct double pair has an open real-line chart
in the actual surface double-pair locus. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem surface_double_pair_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ,
      (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ c.source := by
  obtain ⟨U,F,hU,hxU,hUs,hF,heF⟩ := surface_chart_representative hf x
  obtain ⟨V,G,hV,hyV,hVs,hG,heG⟩ := surface_chart_representative hf y
  let H : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hD : Function.Surjective (fderiv ℝ H (chart x x,chart y y)) :=
    (surface_pair_coordinate_regular_iff x y (hUs hxU) (hVs hyV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hyV))).mp hreg
  obtain ⟨b,hb,hbf,_,_⟩ := double_locus_submersion_chart hH (chart x x,chart y y) hD
  let R : Set (M × M) := (U ×ˢ V) ∩ {z | z.1 ≠ z.2}
  have hR : IsOpen R := (hU.prod hV).inter isClosed_diagonal.isOpen_compl
  let a := ((chart x).prod (chart y)).restrOpen R hR
  let e := a.trans b
  have hp : (x,y) ∈ e.source := by
    exact ⟨⟨⟨hUs hxU,hVs hyV⟩,⟨⟨hxU,hyV⟩,hxy⟩⟩,hb⟩
  apply matched_zero_subset_line_chart e (surfaceDoublePairs f) (x,y) hp ⟨hxy,heq⟩
  intro z hz
  have hsrc : z ∈ (U ×ˢ V) ∩ {z | z.1 ≠ z.2} := hz.1.2
  have hfirst : (e z).1 = f z.1-f z.2 := by
    change (b (chart x z.1,chart y z.2)).1 = _
    rw [hbf]
    change F (chart x z.1)-G (chart y z.2) = _
    change (F ∘ chart x) z.1-(G ∘ chart y) z.2 = _
    rw [← heF hsrc.1.1,← heG hsrc.1.2]
  rw [hfirst,sub_eq_zero]
  exact and_iff_right hsrc.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

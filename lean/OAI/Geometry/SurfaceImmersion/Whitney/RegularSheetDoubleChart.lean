import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveVelocities
import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceRegularLocus

namespace OAI

/-! At a transverse pair of regular points, both projections of a local
smooth double-curve chart are regular. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem regular_sheet_double_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y))
    (hx : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x))
    (hy : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f y)) :
    ∃ c : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ,
      (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ c.source ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.1) c.target ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.2) c.target ∧
      ∀ t ∈ c.target,
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.1) t) ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.2) t) := by
  obtain ⟨c,hp,hA,hB,hpair⟩ := smooth_surface_double_pair_chart hf x y hxy heq hreg
  let R := {p | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  have hR : IsOpen R := surface_regular_locus_open hf
  let J := c.target ∩ {t | (c.symm t).val ∈ R ×ˢ R}
  have hJ : IsOpen J :=
    (continuous_subtype_val.comp_continuousOn c.continuousOn_symm).isOpen_inter_preimage
      c.open_target (hR.prod hR)
  let d := (c.symm.restrOpen J hJ).symm
  have hpJ : c ⟨(x,y),hxy,heq⟩ ∈ J := by
    refine ⟨c.map_source hp,?_⟩
    change (c.symm (c ⟨(x,y),hxy,heq⟩)).val ∈ R ×ˢ R
    rw [c.left_inv hp]
    exact ⟨hx,hy⟩
  have hdp : (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ d.source := ⟨hp,hpJ⟩
  have hdsub : d.target ⊆ c.target := inter_subset_left
  have hAd : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (d.symm t).val.1) d.target :=
    hA.mono hdsub
  have hBd : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (d.symm t).val.2) d.target :=
    hB.mono hdsub
  refine ⟨d,hdp,hAd,hBd,?_⟩
  intro t ht
  have htR : (c.symm t).val ∈ R ×ˢ R := ht.2.2
  apply regular_double_curve_velocities hf
    (hAd.contMDiffAt (d.open_target.mem_nhds ht))
    (hBd.contMDiffAt (d.open_target.mem_nhds ht))
  · exact Filter.Eventually.of_forall fun s => (d.symm s).property.2
  · exact hpair t (hdsub ht)
  · exact htR.1
  · exact htR.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

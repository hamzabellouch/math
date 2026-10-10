import OAI.Geometry.SurfaceImmersion.Geometry.LowerDimensionalImage
import OAI.Geometry.SurfaceImmersion.Geometry.LinearEquivNullImage
import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative

namespace OAI

/-! Smooth two-dimensional images in three-space are null, in the
actual coordinate models used by the surface perturbations. -/
noncomputable section
open Set MeasureTheory Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem euclidean_surface_image_null (f : Base → ProjectionTarget 3) (hf : ContDiff ℝ ∞ f) :
    volume (range f) = 0 := by
  let L : Plane ≃L[ℝ] Base := ContinuousLinearEquiv.ofFinrankEq (by simp [Base])
  let T : ProjectionTarget 3 ≃L[ℝ] Plane × ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hnull := PublishedInputs.smooth_surface_image_volume_zero (T ∘ f ∘ L)
    (T.contDiff.comp (hf.comp L.contDiff))
  have hnull' := linear_equiv_null_image T.symm volume volume hnull
  have he : T.symm '' range (T ∘ f ∘ L) = range f := by
    ext y
    constructor
    · rintro ⟨z,⟨x,rfl⟩,rfl⟩
      exact ⟨L x,by simp⟩
    · rintro ⟨x,rfl⟩
      exact ⟨T (f x),⟨L.symm x,by simp⟩,by simp⟩
  rwa [he] at hnull'

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
theorem compact_surface_image_null (f : M → ProjectionTarget 3)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) : volume (range f) = 0 := by
  choose U F hU hp hsrc hF he using fun p => surface_chart_representative hf p
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun p _ => mem_iUnion.mpr ⟨p,hp p⟩)
  have hsub : range f ⊆ ⋃ p ∈ s, range (F p) := by
    rintro y ⟨x,rfl⟩
    obtain ⟨p,hps,hxp⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact mem_iUnion₂.mpr ⟨p,hps,⟨chart p x,(he p hxp).symm⟩⟩
  apply measure_mono_null hsub
  exact (measure_biUnion_null_iff s.finite_toSet.countable).mpr (fun p _ => euclidean_surface_image_null (F p) (hF p))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

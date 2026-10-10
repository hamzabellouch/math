import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative
import OAI.Geometry.SurfaceImmersion.Atlas.ChartGermImmersion

namespace OAI

/-! The regular locus of a smooth surface map is open in the actual surface. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_regular_locus_open {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    IsOpen {p | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨U,F,hU,hpU,hUs,hF,heF⟩ := surface_chart_representative hf p
  let V : Set Base := {z | Function.Injective (fderiv ℝ F z)}
  have hV : IsOpen V := ContinuousLinearMap.isOpen_injective.preimage
    (hF.continuous_fderiv (by simp))
  have hpV : chart p p ∈ V :=
    (chart_germ_immersion_iff p (hUs hpU) hF
      (heF.eventuallyEq_of_mem (hU.mem_nhds hpU))).mp hp
  have hW : IsOpen (U ∩ (chart p) ⁻¹' V) :=
    ((chart p).continuousOn.mono hUs).isOpen_inter_preimage hU hV
  apply Filter.mem_of_superset (hW.mem_nhds ⟨hpU,hpV⟩)
  rintro x ⟨hxU,hxV⟩
  exact (chart_germ_immersion_iff p (hUs hxU) hF
    (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))).mpr hxV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

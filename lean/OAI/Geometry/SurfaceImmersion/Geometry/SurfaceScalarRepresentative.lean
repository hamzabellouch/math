import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairDerivative
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! Every smooth scalar surface function has a globally smooth Euclidean
representative on an actual smaller neighborhood of any chosen point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem scalar_surface_chart_representative {f : M → ℝ}
    (hf : ContMDiff planeModel 𝓘(ℝ,ℝ) ∞ f) (p : M) :
    ∃ (U : Set M) (F : Base → ℝ), IsOpen U ∧ p ∈ U ∧
      U ⊆ (chart p).source ∧ ContDiff ℝ ∞ F ∧ EqOn f (F ∘ chart p) U := by
  have hp : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨W,hW,hpW,hWT,F,hF,hFF⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := chart p p)) (chart p).open_target
    (singleton_subset_iff.mpr ((chart p).map_source hp)) hlocal
  let U := (chart p).source ∩ (chart p) ⁻¹' W
  refine ⟨U,F,(chart p).isOpen_inter_preimage hW,⟨hp,hpW (mem_singleton _)⟩,
    inter_subset_left,hF,?_⟩
  intro x hx
  change f x = F (chart p x)
  rw [hFF hx.2]
  change f x = f ((chart p).symm (chart p x))
  rw [(chart p).left_inv hx.1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

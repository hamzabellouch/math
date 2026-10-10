import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative

namespace OAI

/-! Smooth representatives on a fixed compact part of a surface chart.
The compact chart region can be chosen before the surface map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem surface_compact_representative {f : M → W}
    (hf : ContMDiff planeModel 𝓘(ℝ,W) ∞ f) (p : M)
    {K : Set M} (hK : IsCompact K) (hKp : K ⊆ (chart p).source) :
    ∃ F : Base → W, ContDiff ℝ ∞ F ∧ EqOn f (F ∘ chart p) K := by
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  have hKc : IsCompact ((chart p) '' K) :=
    hK.image_of_continuousOn ((chart p).continuousOn.mono hKp)
  have hKT : (chart p) '' K ⊆ (chart p).target := by
    rintro z ⟨x,hx,rfl⟩
    exact (chart p).map_source (hKp hx)
  obtain ⟨U,hU,hKU,hUT,F,hF,hFF⟩ := CollarVelocity.compact_smooth_extension
    hKc (chart p).open_target hKT hlocal
  refine ⟨F,hF,?_⟩
  intro x hx
  change f x = F (chart p x)
  rw [hFF (hKU ⟨x,hx,rfl⟩)]
  change f x = f ((chart p).symm (chart p x))
  rw [(chart p).left_inv (hKp hx)]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceCrosscapNormalForm
import OAI.Geometry.SurfaceImmersion.Whitney.SimplePreparedCrosscaps

namespace OAI

/-! The unconditional generic map has actual standard crosscap charts,
with globally isolated singular values and transverse regular sheets. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure SurfaceCrosscapCoordinates (f : M → ProjectionTarget 3) (p : M) where
  source : OpenPartialHomeomorph M Base
  target : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)
  source_mem : p ∈ source.source
  source_center : source p = 0
  target_mem : 0 ∈ target.source
  target_center : target 0 = f p
  source_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ source source.source
  source_inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ source.symm source.target
  target_smooth : ContDiff ℝ ∞ target
  target_inverse_smooth : ContDiffOn ℝ ∞ target.symm target.target
  model_mem : ∀ x ∈ source.source, standardCrosscap (source x) ∈ target.source
  model_eq : ∀ x ∈ source.source, f x = target (standardCrosscap (source x))

theorem exists_standard_prepared_crosscap_map [CompactSpace M] [T2Space M] :
    ∃ f : M → ProjectionTarget 3,
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite ∧
      (∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y)) ∧
      (∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
        ∀ q, f q = f p → q = p) ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
        Nonempty (SurfaceCrosscapCoordinates f p) := by
  obtain ⟨f,hf,hfin,hreg,hsimple,hrep⟩ := exists_simple_prepared_crosscap_map (M := M)
  refine ⟨f,hf,hfin,hreg,hsimple,?_⟩
  intro p hp
  obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hR⟩ := hrep p hp
  obtain ⟨c,e,hpc,hcp,h0e,he0,hcS,hcI,heS,heI,heq⟩ :=
    surface_crosscap_normal_form f p q hpq hφ he b t hz hR
  exact ⟨⟨c,e,hpc,hcp,h0e,he0,hcS,hcI,heS,heI,
    fun x hx => (heq x hx).1,fun x hx => (heq x hx).2⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

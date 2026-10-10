import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceImmersionLocalInjective
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapFiberIsolation

namespace OAI

/-! Every fiber of the actual prepared map is finite: regular points are
locally injective, and the prepared crosscaps are isolated in their fibers. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

theorem prepared_surface_finite_fiber {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (y : ProjectionTarget 3) : {p | f p = y}.Finite := by
  classical
  have hcompact : IsCompact {p | f p = y} :=
    (isClosed_eq hf.continuous continuous_const).isCompact
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  have hlocal : ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, f x = f p → x = p := by
    by_cases hreg : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)
    · obtain ⟨U,hU,hpU,hinj⟩ := surface_immersion_locally_injective hf p hreg
      exact ⟨U,hU,hpU,fun x hx h => hinj hx hpU h⟩
    · obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hR⟩ := hrep p hreg
      exact prepared_crosscap_isolated_fiber p q hpq hφ he b t hz hR
  obtain ⟨U,hU,hpU,hiso⟩ := hlocal
  refine ⟨U,hU,?_⟩
  ext x
  constructor
  · rintro ⟨hxU,hx⟩
    exact mem_singleton_iff.mpr (hiso x hxU (hx.trans hp.symm))
  · rintro rfl
    exact ⟨hpU,hp⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

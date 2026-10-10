import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveBoundaryPaths
import OAI.Geometry.SurfaceImmersion.Whitney.CurveBoundaryEmbeddedArc

namespace OAI

/-! Every actual crosscap endpoint is joined to another one by an
embedded arc of the compactified double curve, with regular interior. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_double_curve_boundary_arc {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∀ p : doubleCurveBoundary f, ∃ q : doubleCurveBoundary f, q ≠ p ∧
      ∃ γ : Path p.val q.val, IsClosedEmbedding γ ∧
        ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∉ doubleCurveBoundary f := by
  obtain ⟨V,P,hV,hDV,hP,hdis,hcover,hw,_⟩ := prepared_double_curve_boundary_paths hf hfin hreg hrep
  exact curve_boundary_embedded_arc (doubleCurveBoundary f) V hDV hV P
    (fun E hE => ⟨(hP E hE).1,(hP E hE).2.2⟩) hdis hcover hw
    (transverse_double_curve_interior_chart hf hreg)
    (transverse_double_curve_boundary_chart hf hrep)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

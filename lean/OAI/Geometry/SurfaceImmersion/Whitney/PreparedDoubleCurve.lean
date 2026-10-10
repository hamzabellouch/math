import OAI.Geometry.SurfaceImmersion.Whitney.CompactifiedDoubleCurve

namespace OAI

/-! An unconditional prepared surface map with a compact unordered double
curve and exactly its finite singular set as the diagonal endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_prepared_compactified_double_map :
    ∃ F : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p)}.Finite ∧
      IsCompact (compactifiedDoubleCurve F) ∧
      (∀ p, unorderedPair (p,p) ∈ compactifiedDoubleCurve F ↔
        ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p)) ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p) →
        ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
          p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
          F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
          surfaceDirection φ b (chart q p,t) = 0 ∧
          Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)) := by
  obtain ⟨F,hF,hfin,hrep⟩ := exists_finite_quadratic_crosscap_map (M := M)
  refine ⟨F,hF,hfin,compactifiedDoubleCurve_compact F,?_,hrep⟩
  intro p
  rw [compactifiedDoubleCurve_diagonal]
  refine ⟨doublePairs_closure_diagonal_singular hF p,?_⟩
  intro hp
  obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hreg⟩ := hrep p hp
  exact crosscap_diagonal_mem_closure F p q hpq hφ he b t hz hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

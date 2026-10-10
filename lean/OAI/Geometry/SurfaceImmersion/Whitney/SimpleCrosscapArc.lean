import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapOrderedArc
import OAI.Geometry.SurfaceImmersion.Whitney.ClosedDoubleArcLift
import OAI.Geometry.SurfaceImmersion.Whitney.SimplePreparedCrosscaps

namespace OAI

/-! For the prepared map with simple singular fibers, the connecting ordered
arc has two regular sheets at every interior point. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem simple_prepared_crosscap_ordered_arc {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hsimple : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∀ q, f q = f p → q = p)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (p : M) (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ q : M, q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
      ∃ Γ : Path (p,p) (q,q), IsClosedEmbedding Γ ∧
        (∀ t, f (Γ t).1 = f (Γ t).2) ∧
        (∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2 ∧
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).1) ∧
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).2)) := by
  classical
  obtain ⟨q,hqp,hq,Γ,hΓ,heq,hne⟩ := prepared_crosscap_ordered_arc hf hfin hreg hrep p hp
  refine ⟨q,hqp,hq,Γ,hΓ,heq,?_⟩
  intro t ht0 ht1
  have htne := hne t ht0 ht1
  refine ⟨htne,?_,?_⟩
  · by_contra hbad
    exact htne (hsimple (Γ t).1 hbad (Γ t).2 (heq t).symm).symm
  · by_contra hbad
    exact htne (hsimple (Γ t).2 hbad (Γ t).1 (heq t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

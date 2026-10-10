import OAI.Geometry.SurfaceImmersion.Whitney.FiniteExceptionalDoublePairs
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapOrderedArc

namespace OAI

/-! Along an embedded ordered double arc, only finitely many parameter
values can meet any of the finitely many singular points of the prepared map. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma double_arc_exceptional_times_finite {X Y T : Type*} (f : X → Y)
    (hfin : ∀ y, {x | f x = y}.Finite) {S : Set X} (hS : S.Finite)
    (Γ : T → X × X) (hΓ : Function.Injective Γ)
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2) :
    {t | (Γ t).1 ∈ S ∨ (Γ t).2 ∈ S}.Finite := by
  have hbad := finite_exceptional_double_pairs f hfin hS
  have hpre := hbad.preimage hΓ.injOn
  exact hpre.subset (fun t ht => ⟨ht,heq t⟩)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_crosscap_ordered_arc_regular {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
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
        (∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) ∧
        {t : I | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).1) ∨
          ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).2)}.Finite := by
  obtain ⟨q,hqp,hq,Γ,hΓ,hΓeq,hΓne⟩ := prepared_crosscap_ordered_arc hf hfin hreg hrep p hp
  refine ⟨q,hqp,hq,Γ,hΓ,hΓeq,hΓne,?_⟩
  exact double_arc_exceptional_times_finite f (prepared_surface_finite_fiber hf hrep)
    hfin Γ hΓ.injective hΓeq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

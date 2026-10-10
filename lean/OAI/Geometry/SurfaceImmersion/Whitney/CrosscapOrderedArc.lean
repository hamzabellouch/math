import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveBoundaryArc
import OAI.Geometry.SurfaceImmersion.Whitney.ClosedDoubleArcLift

namespace OAI

/-! The prepared surface map has a continuously parametrized ordered
double arc connecting each crosscap to a distinct crosscap. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_crosscap_ordered_arc {f : M → ProjectionTarget 3}
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
        (∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) := by
  obtain ⟨c,φ,b,s,hpc,hφ,he,hz,hR⟩ := hrep p hp
  have hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve f :=
    (compactifiedDoubleCurve_diagonal f p).mpr (crosscap_diagonal_mem_closure f p c hpc hφ he b s hz hR)
  let P : doubleCurveBoundary f := ⟨⟨unorderedPair (p,p),hpK⟩,p,rfl⟩
  obtain ⟨Q,hQP,γ,hγ,hinter⟩ := prepared_double_curve_boundary_arc hf hfin hreg hrep P
  obtain ⟨q,hqeq⟩ := Q.property
  have hqp : q ≠ p := by
    intro h
    apply hQP
    apply Subtype.ext
    apply Subtype.ext
    exact hqeq.symm.trans (congrArg (fun x => unorderedPair (x,x)) h)
  have hqK : unorderedPair (q,q) ∈ compactifiedDoubleCurve f := hqeq.symm ▸ Q.val.property
  have hq : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) :=
    doublePairs_closure_diagonal_singular hf q ((compactifiedDoubleCurve_diagonal f q).mp hqK)
  let γU : Path (unorderedPair (p,p)) (unorderedPair (q,q)) :=
    (γ.map continuous_subtype_val).cast rfl hqeq
  have hγU : Function.Injective γU := Subtype.val_injective.comp hγ.injective
  have hgood : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γU t ∈ unorderedDistinctPairs M := by
    intro t ht0 ht1 hbad
    exact hinter t ht0 ht1 hbad
  obtain ⟨Γ,hΓ,hΓeq⟩ := embedded_closed_double_arc_lift p q γU hγU hgood
  refine ⟨q,hqp,hq,Γ,hΓ,?_,?_⟩
  · intro t
    apply compactifiedDoubleCurve_pair_equality hf
    rw [hΓeq]
    exact (γ t).property
  · intro t ht0 ht1
    apply (unorderedPair_mem_distinct_iff (Γ t)).mp
    rw [hΓeq]
    exact hgood t ht0 ht1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceCrosscapTransverseNeighborhood

namespace OAI

/-! Disjoint compact frozen neighborhoods inside the actual quadratic
crosscap charts. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_crosscap_neighborhoods
    {f : M → ProjectionTarget 3}
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
    ∃ A : S → Set M, (∀ i, IsCompact (A i) ∧ i.val ∈ interior (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ regularSurfacePairs f := by
  classical
  dsimp only
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  obtain ⟨V,hV,hd⟩ := hfin.t2_separation
  have hex (p : S) : ∃ A : Set M, IsCompact A ∧ p.val ∈ interior A ∧ A ⊆ V p.val ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (x,y) ∈ regularSurfacePairs f := by
    obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hreg⟩ := hrep p p.property
    obtain ⟨W,hW,hpW,hgood⟩ := crosscap_transverse_neighborhood f p q hpq hφ he b t hz hreg
    obtain ⟨A,hA,hpA,hsub⟩ := exists_compact_subset ((hV p.val).2.inter hW) ⟨(hV p.val).1,hpW⟩
    exact ⟨A,hA,hpA,fun _ hx => (hsub hx).1,
      fun x hx y hy hxy => hgood x (hsub hx).2 y (hsub hy).2 hxy⟩
  choose A hA hpA hAV hgood using hex
  refine ⟨A,fun p => ⟨hA p,hpA p⟩,?_,hgood⟩
  intro p q hpq
  exact (hd p.property q.property (fun h => hpq (Subtype.ext h))).mono (hAV p) (hAV q)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Whitney.FiniteDoubleCurvePieces
import OAI.Geometry.SurfaceImmersion.Geometry.CurveIncidenceBoundaryPair

namespace OAI

/-! The prepared self-transverse surface map has actual finite paths
joining every crosscap endpoint to another crosscap endpoint. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_double_curve_boundary_paths {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ (V : Set (compactifiedDoubleCurve f)) (P : Finset (Set (compactifiedDoubleCurve f))),
      V.Finite ∧ doubleCurveBoundary f ⊆ V ∧
      (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧ Vᶜ = ⋃ E ∈ P, E ∧
      (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) ∧
      ∀ p : doubleCurveBoundary f, ∃ q : doubleCurveBoundary f, q ≠ p ∧
        ∃ (hp : p.val ∈ V) (hq : q.val ∈ V), Nonempty
          ((curveIncidenceGraph V P).Path (Sum.inl ⟨p.val,hp⟩) (Sum.inl ⟨q.val,hq⟩)) := by
  let : CompactSpace (compactifiedDoubleCurve f) :=
    isCompact_iff_compactSpace.mp (compactifiedDoubleCurve_compact f)
  have hline := transverse_double_curve_interior_chart hf hreg
  have hhalf := transverse_double_curve_boundary_chart hf hrep
  obtain ⟨V,P,hV,hDV,hP,hdis,hcover,hw⟩ := compact_curve_pieces (doubleCurveBoundary f)
    (doubleCurveBoundary_finite hf hfin) (fun p => by
      by_cases hp : p ∈ doubleCurveBoundary f
      · exact Or.inr (hhalf p hp)
      · exact Or.inl (hline p hp))
  refine ⟨V,P,hV,hDV,hP,hdis,hcover,hw,?_⟩
  intro p
  obtain ⟨q,hqp,hpath⟩ := curve_boundary_pair (doubleCurveBoundary f) V hDV hV P
    (fun E hE => ⟨(hP E hE).1,(hP E hE).2.2⟩) hdis hcover hw hline hhalf p
  exact ⟨q,hqp,hDV p.property,hDV q.property,hpath⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

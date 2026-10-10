import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapPathInterior
import OAI.Geometry.SurfaceImmersion.Whitney.SimpleCrosscapArc

namespace OAI

/-! Actual finite regular embedded source connections for the prepared
map, with no interior singular points. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_crosscap_source_path {f : M → ProjectionTarget 3}
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
      ∃ P : Path p q, FiniteRegularPath planeModel P ∧ Function.Injective P ∧
        ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 →
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P t)) := by
  obtain ⟨q,hqp,hq,Γ,hΓ,heq,hgood⟩ := simple_prepared_crosscap_ordered_arc hf hfin hreg hsimple hrep p hp
  have hcoords (x : M) (hx : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
      Nonempty (SurfaceCrosscapCoordinates f x) := by
    obtain ⟨c,φ,b,t,hxc,hφ,he,hz,hR⟩ := hrep x hx
    obtain ⟨C,T,hxC,hCx,h0T,hT0,hCS,hCI,hTS,hTI,hmodel⟩ :=
      surface_crosscap_normal_form f x c hxc hφ he b t hz hR
    exact ⟨⟨C,T,hxC,hCx,h0T,hT0,hCS,hCI,hTS,hTI,
      fun y hy => (hmodel y hy).1,fun y hy => (hmodel y hy).2⟩⟩
  obtain ⟨P,hPp,hPi,_,hPr⟩ := crosscap_source_embedded_path_regular hf hreg
    (hcoords p hp).some (hcoords q hq).some Γ.continuous hΓ.injective Γ.source Γ.target heq hgood (hsimple p hp)
  exact ⟨q,hqp,hq,P,hPp,hPi,hPr⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

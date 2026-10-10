import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCrosscapSourceGeometry
import OAI.Geometry.SurfaceImmersion.Whitney.SimpleCrosscapArc

namespace OAI

/-! The actual generic surface map admits a smooth embedded regular
source connection between a chosen crosscap and a distinct crosscap,
with both original kernel-axis endpoint coordinates retained. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_smooth_crosscap_arc {f : M → ProjectionTarget 3}
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
    ∃ (q : M) (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
      (P : SmoothCompactArc planeModel M) (V W : Set M),
      q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
      IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ q ∈ W ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      (∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t))) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ V →
        P.curve t ∈ cp.source.source ∧ cp.source (P.curve t) 0 = 0) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ W →
        P.curve t ∈ cq.source.source ∧ cq.source (P.curve t) 0 = 0) := by
  obtain ⟨q,hqp,hq,Γ,hΓ,heq,hgood⟩ := simple_prepared_crosscap_ordered_arc hf hfin hreg hsimple hrep p hp
  have hcoords (x : M) (hx : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
      Nonempty (SurfaceCrosscapCoordinates f x) := by
    obtain ⟨c,φ,b,t,hxc,hφ,he,hz,hR⟩ := hrep x hx
    obtain ⟨C,T,hxC,hCx,h0T,hT0,hCS,hCI,hTS,hTI,hmodel⟩ :=
      surface_crosscap_normal_form f x c hxc hφ he b t hz hR
    exact ⟨⟨C,T,hxC,hCx,h0T,hT0,hCS,hCI,hTS,hTI,
      fun y hy => (hmodel y hy).1,fun y hy => (hmodel y hy).2⟩⟩
  let cp := (hcoords p hp).some
  let cq := (hcoords q hq).some
  obtain ⟨P,V,W,h⟩ := smooth_crosscap_source_geometry hf hreg cp cq hp hq Γ.continuous
    hΓ.injective Γ.source Γ.target heq hgood (hsimple p hp) (hsimple q hq)
  exact ⟨q,cp,cq,P,V,W,hqp,hq,h⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

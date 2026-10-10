import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisEndpointGerms
import OAI.Geometry.SurfaceImmersion.Whitney.PreparedSmoothCrosscapArc

namespace OAI

/-! Actual geometric data for transporting the crosscap-pair replacement.
The arc is embedded and smooth through both endpoint kernel axes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

structure CrosscapConnectingArc (f : M → ProjectionTarget 3) (p q : M) where
  left : SurfaceCrosscapCoordinates f p
  right : SurfaceCrosscapCoordinates f q
  arc : SmoothCompactArc planeModel M
  source : arc.curve arc.start = p
  target : arc.curve arc.finish = q
  regular : ∀ t ∈ Ioo arc.start arc.finish,
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (arc.curve t))
  leftParameter : ℝ ≃ₜ ℝ
  rightParameter : ℝ ≃ₜ ℝ
  left_smooth : ContDiff ℝ ∞ leftParameter
  left_inverse_smooth : ContDiff ℝ ∞ leftParameter.symm
  right_smooth : ContDiff ℝ ∞ rightParameter
  right_inverse_smooth : ContDiff ℝ ∞ rightParameter.symm
  left_zero : leftParameter arc.start = 0
  right_zero : rightParameter arc.finish = 0
  left_germ : arc.curve =ᶠ[𝓝 arc.start] left.axisCurve ∘ leftParameter
  right_germ : arc.curve =ᶠ[𝓝 arc.finish] right.axisCurve ∘ rightParameter

theorem exists_crosscap_connecting_arc [CompactSpace M] {f : M → ProjectionTarget 3}
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
      Nonempty (CrosscapConnectingArc f p q) := by
  obtain ⟨q,cp,cq,P,V,W,hqp,hq,hV,hpV,hW,hqW,hPs,hPf,hPr,hleft,hright⟩ :=
    prepared_smooth_crosscap_arc hf hfin hreg hsimple hrep p hp
  obtain ⟨R,e₀,e₁,hRs,hRf,hRP,h₀s,h₀i,h₀0,h₁s,h₁i,h₁0,hleft',hright'⟩ :=
    crosscap_axis_endpoint_germs cp cq P hPs hPf hV hpV hW hqW hleft hright
  refine ⟨q,hqp,hq,⟨⟨cp,cq,R,?_,?_,?_,e₀,e₁,h₀s,h₀i,h₁s,h₁i,?_,?_,?_,?_⟩⟩⟩
  · rw [hRs,hRP (left_mem_Icc.mpr P.start_lt_finish.le),hPs]
  · rw [hRf,hRP (right_mem_Icc.mpr P.start_lt_finish.le),hPf]
  · intro t ht
    rw [hRs,hRf] at ht
    rw [hRP ⟨ht.1.le,ht.2.le⟩]
    exact hPr t ht
  · rwa [hRs]
  · rwa [hRf]
  · rwa [hRs]
  · rwa [hRf]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

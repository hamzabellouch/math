import OAI.Analysis.KadisonKastler.RealRectangularFunctionalCalculus
import OAI.Analysis.KadisonKastler.GraphIsometryTransport
import OAI.Analysis.KadisonKastler.TomitaPolarResolventSymmetry

namespace OAI

/-! # Polar conjugations along a reducing graph isometry -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (V : H →ₗᵢ[ℂ] K) (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K) (Ω : H) (ξ : K)
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hMcyc : DenseRange (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))
  (hNcyc : DenseRange (algebraVectorMap N ξ))
  (hforward : ∀ a : Algebra M, graphIsometry V J L (rescaledGraphVector J Ω 1 a.val) ∈
    rescaledGraphSubspace N L ξ 1)
  (hback : ∀ b : Algebra N,
    (graphIsometry V J L).toContinuousLinearMap.adjoint (rescaledGraphVector L ξ 1 b.val) ∈
      rescaledGraphSubspace M J Ω 1)

include hforward hback in
theorem tomitaGraphRoot_isometry (x : H) :
    tomitaGraphRoot (M := N) L ξ (V x) = V (tomitaGraphRoot (M := M) J Ω x) := by
  have hr : (graphResolvent N L ξ 1).comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp (graphResolvent M J Ω 1) := by
    ext y
    exact graphIsometry_resolvent V J L Ω ξ 1 hforward hback y
  exact congrArg (fun T : H →L[ℂ] K => T x)
    (sqrt_rectangular_intertwines _ _ V.toContinuousLinearMap
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (graphResolvent_positive L ξ 1))
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (graphResolvent_positive J Ω 1)) hr)

include hforward hback in
theorem tomitaPolarConjugation_isometry (x : H) :
    tomitaPolarConjugation L ξ hNsep hNcyc (V x) =
      V (tomitaPolarConjugation J Ω hMsep hMcyc x) := by
  have hmap {v : TomitaGraphHilbert H} (hv : v ∈ rescaledGraphSubspace M J Ω 1) :
      graphIsometry V J L v ∈ rescaledGraphSubspace N L ξ 1 := by
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω 1)) ?_
      ((Submodule.isClosed_topologicalClosure _).preimage (graphIsometry V J L).continuous) hv
    rintro _ ⟨a,rfl⟩
    exact hforward a
  let v : rescaledGraphSubspace N L ξ 1 :=
    ⟨graphIsometry V J L (tomitaPolarCoordinates J Ω hMsep hMcyc x).val,
      hmap (tomitaPolarCoordinates J Ω hMsep hMcyc x).property⟩
  have he : tomitaPolarCoordinates L ξ hNsep hNcyc (V x)=v := by
    apply tomitaGraphFirst_injective L ξ hNsep
    simp only [tomitaGraphFirst_apply]
    change (tomitaPolarCoordinates L ξ hNsep hNcyc (V x)).val 0 =
      graphIsometry V J L (tomitaPolarCoordinates J Ω hMsep hMcyc x).val 0
    rw [tomitaPolarCoordinates_first, graphIsometry_zero, tomitaPolarCoordinates_first]
    exact tomitaGraphRoot_isometry V J L Ω ξ hforward hback x
  have hsecond := congrArg (fun y : rescaledGraphSubspace N L ξ 1 => y.val 1) he
  change (tomitaPolarCoordinates L ξ hNsep hNcyc (V x)).val 1 =
    graphIsometry V J L (tomitaPolarCoordinates J Ω hMsep hMcyc x).val 1 at hsecond
  rw [tomitaPolarCoordinates_second, graphIsometry_one, tomitaPolarCoordinates_second,
    J.symm_apply_apply] at hsecond
  apply tomitaGraphRoot_injective L ξ hNsep hNcyc
  rw [tomitaGraphRoot_isometry V J L Ω ξ hforward hback]
  exact L.injective hsecond

end
end KadisonKastler

end OAI

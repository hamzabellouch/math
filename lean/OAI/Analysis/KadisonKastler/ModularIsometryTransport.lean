import OAI.Analysis.KadisonKastler.RectangularFunctionalCalculus
import OAI.Analysis.KadisonKastler.ModularStrongContinuity

namespace OAI

/-! # Transport of the modular group along a reducing Hilbert isometry -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K) (Ω : H) (ξ : K)
  (V : H →ₗᵢ[ℂ] K)
  (hR : ∀ x, graphResolvent N L ξ 1 (V x) = V (graphResolvent M J Ω 1 x))

include hR in
theorem modularApproximation_isometry (n : ℕ) (t : ℝ) (x : H) :
    modularApproximation N L ξ n t (V x) = V (modularApproximation M J Ω n t x) := by
  have he : (graphResolvent N L ξ 1).comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp (graphResolvent M J Ω 1) := by
    ext y
    exact hR y
  have h := cfc_rectangular_intertwines _ _ V.toContinuousLinearMap
    (graphResolvent_positive L ξ 1).isSelfAdjoint
    (graphResolvent_positive J Ω 1).isSelfAdjoint he
    (modularPhaseScalar t (modularRegularizationScale n))
    (modularPhaseScalar_continuousOn L ξ t (modularRegularizationScale_pos n))
    (modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n))
  have hx := congrArg (fun T : H →L[ℂ] K => T x) h
  change (regularizedModularGroup N L ξ (modularRegularizationScale n)
    (Multiplicative.ofAdd t) : K →L[ℂ] K) (V x) =
    V ((regularizedModularGroup M J Ω (modularRegularizationScale n)
      (Multiplicative.ofAdd t) : H →L[ℂ] H) x)
  rw [regularizedModularGroup_eq_cfc L ξ t (modularRegularizationScale_pos n),
    regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n)]
  exact hx

variable [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hMcyc : DenseRange (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))
  (hNcyc : DenseRange (algebraVectorMap N ξ))

include hR in
theorem modularStrongGroup_isometry (t : Multiplicative ℝ) (x : H) :
    (modularStrongGroup L ξ hNsep hNcyc t : K →L[ℂ] K) (V x) =
      V ((modularStrongGroup J Ω hMsep hMcyc t : H →L[ℂ] H) x) := by
  have hK := modularApproximation_tendsto L ξ hNsep hNcyc t.toAdd (V x)
  have hH := V.continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hMsep hMcyc t.toAdd x)
  have he (n : ℕ) := modularApproximation_isometry J L Ω ξ V hR n t.toAdd x
  change Tendsto (fun n => V (modularApproximation M J Ω n t.toAdd x)) atTop
    (𝓝 (V (modularStrongLimit J Ω hMsep hMcyc t.toAdd x))) at hH
  simp_rw [← he] at hH
  exact tendsto_nhds_unique hK hH

end

end KadisonKastler

end OAI

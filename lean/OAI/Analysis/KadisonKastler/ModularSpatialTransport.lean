import OAI.Analysis.KadisonKastler.ModularStrongContinuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

namespace OAI

/-! # Spatial transport of the constructed modular group

Intertwining the bounded graph resolvent suffices: its continuous phase
approximations intertwine, and so do their strong limits.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (J : H ≃ₗᵢ⋆[ℂ] H) (L : K ≃ₗᵢ⋆[ℂ] K) (Ω : H) (ξ : K)
  (hMsep : Function.Injective (algebraVectorMap M Ω))
  (hMcyc : DenseRange (algebraVectorMap M Ω))
  (hNsep : Function.Injective (algebraVectorMap N ξ))
  (hNcyc : DenseRange (algebraVectorMap N ξ))
  (V : H ≃ₗᵢ[ℂ] K)
  (hR : V.conjStarAlgEquiv (graphResolvent M J Ω 1) = graphResolvent N L ξ 1)

omit [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K] in
include hR in
theorem modularApproximation_spatial (n : ℕ) (t : ℝ) (x : H) :
    V (modularApproximation M J Ω n t x) = modularApproximation N L ξ n t (V x) := by
  have he : V.conjStarAlgEquiv (modularApproximation M J Ω n t) =
      modularApproximation N L ξ n t := by
    change V.conjStarAlgEquiv
      (regularizedModularGroup M J Ω (modularRegularizationScale n)
        (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (regularizedModularGroup N L ξ (modularRegularizationScale n)
        (Multiplicative.ofAdd t) : K →L[ℂ] K)
    rw [regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n),
      regularizedModularGroup_eq_cfc L ξ t (modularRegularizationScale_pos n)]
    have hc := StarAlgHomClass.map_cfc V.conjStarAlgEquiv
      (modularPhaseScalar t (modularRegularizationScale n)) (graphResolvent M J Ω 1)
      (modularPhaseScalar_continuousOn J Ω t (modularRegularizationScale_pos n))
      (by fun_prop) (graphResolvent_positive J Ω 1).isSelfAdjoint.isStarNormal
      (by rw [hR]; exact (graphResolvent_positive L ξ 1).isSelfAdjoint.isStarNormal)
    rw [hR] at hc
    exact hc
  have hx := congrArg (fun A : K →L[ℂ] K => A (V x)) he
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] using hx

include hR in
theorem modularStrongGroup_spatial (t : Multiplicative ℝ) (x : H) :
    V ((modularStrongGroup J Ω hMsep hMcyc t : H →L[ℂ] H) x) =
      (modularStrongGroup L ξ hNsep hNcyc t : K →L[ℂ] K) (V x) := by
  have hh := V.continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hMsep hMcyc t.toAdd x)
  have hk := modularApproximation_tendsto L ξ hNsep hNcyc t.toAdd (V x)
  have he (n : ℕ) := modularApproximation_spatial J L Ω ξ V hR n t.toAdd x
  change Tendsto (fun n => V (modularApproximation M J Ω n t.toAdd x)) atTop
    (𝓝 (V (modularStrongLimit J Ω hMsep hMcyc t.toAdd x))) at hh
  simp_rw [he] at hh
  exact tendsto_nhds_unique hh hk

end

end KadisonKastler

end OAI

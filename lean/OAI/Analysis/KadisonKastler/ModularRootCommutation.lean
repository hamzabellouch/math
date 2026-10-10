import OAI.Analysis.KadisonKastler.ModularPolarSymmetry

namespace OAI

/-! # The modular group commutes with the graph square root -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modularApproximation_commute_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (n : ℕ) (t : ℝ) :
    Commute (modularApproximation M J Ω n t) (graphResolvent M J Ω 1) := by
  change Commute (regularizedModularGroup M J Ω (modularRegularizationScale n)
    (Multiplicative.ofAdd t) : H →L[ℂ] H) _
  rw [regularizedModularGroup_eq_cfc J Ω t (modularRegularizationScale_pos n)]
  exact (graphResolvent_positive J Ω 1).isSelfAdjoint.commute_cfc
    (Commute.refl _) (modularPhaseScalar t (modularRegularizationScale n))

variable [TopologicalSpace.SeparableSpace H]

theorem modularStrongGroup_commute_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (graphResolvent M J Ω 1) := by
  apply ContinuousLinearMap.ext
  intro x
  change modularStrongLimit J Ω hsep hcyc t (graphResolvent M J Ω 1 x) =
    graphResolvent M J Ω 1 (modularStrongLimit J Ω hsep hcyc t x)
  have hu := modularApproximation_tendsto J Ω hsep hcyc t (graphResolvent M J Ω 1 x)
  have hv := (graphResolvent M J Ω 1).continuous.continuousAt.tendsto.comp
    (modularApproximation_tendsto J Ω hsep hcyc t x)
  apply tendsto_nhds_unique hu
  convert hv using 1
  funext n
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (modularApproximation_commute_resolvent J Ω n t).eq

theorem modularStrongGroup_commute_root (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (t : ℝ) :
    Commute (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
      (tomitaGraphRoot (M := M) J Ω) := by
  rw [tomitaGraphRoot, CFC.sqrt_eq_cfc]
  exact ((modularStrongGroup_commute_resolvent J Ω hsep hcyc t).symm.cfc_nnreal NNReal.sqrt).symm

end

end KadisonKastler

end OAI

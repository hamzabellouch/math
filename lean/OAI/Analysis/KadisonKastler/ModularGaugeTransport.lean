import OAI.Analysis.KadisonKastler.CyclicGaugeIdentity
import OAI.Analysis.KadisonKastler.L2FourierIntertwining

namespace OAI

/-! # Transporting the cyclic Fourier gauge identity to the original space -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

def modularUpperCutField (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : ℝ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  regularFieldOperator volume (fun ξ => modularUpperCut M J Ω (a - 2 * Real.pi * ξ))
    (modularUpperCut_measurable J Ω a) 1
    (Filter.Eventually.of_forall fun _ => modularUpperCut_contracts J Ω _)

variable (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

def modularCyclicEmbedding : ModularCyclicSpace M J Ω x →L[ℂ] H :=
  (resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint x).toContinuousLinearMap

theorem modularCyclicEmbedding_group (t : Multiplicative ℝ) (v : ModularCyclicSpace M J Ω x) :
    modularCyclicEmbedding (M := M) J Ω x ((modularCyclicGroup J Ω hsep hcyc x t :
      ModularCyclicSpace M J Ω x →L[ℂ] ModularCyclicSpace M J Ω x) v) =
    (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) (modularCyclicEmbedding (M := M) J Ω x v) :=
  modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x t.toAdd v

theorem modularCyclicEmbedding_cutField (a : ℝ)
    (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    (modularCyclicEmbedding (M := M) J Ω x).compLp (modularCyclicCutField M J Ω x a F) =
      modularUpperCutField M J Ω a ((modularCyclicEmbedding (M := M) J Ω x).compLp F) := by
  apply compLp_regularFieldOperator volume (modularCyclicEmbedding (M := M) J Ω x)
    (fun ξ => modularCyclicCut M J Ω x (a - 2 * Real.pi * ξ))
    (fun ξ => modularUpperCut M J Ω (a - 2 * Real.pi * ξ))
    (modularCyclicCut_measurable J Ω x a) (modularUpperCut_measurable J Ω a) 1 1
    (Filter.Eventually.of_forall fun _ => modularCyclicCut_contracts J Ω x _)
    (Filter.Eventually.of_forall fun _ => modularUpperCut_contracts J Ω _)
  intro ξ v
  exact modularCyclicCut_intertwines J Ω x _ v

theorem modularCyclicEmbedding_gauge_fourier (a : ℝ)
    (F : RegularCoreHilbert (ModularCyclicSpace M J Ω x)) :
    (𝓕 ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          ((modularCyclicEmbedding (M := M) J Ω x).compLp F)))) : RegularCoreHilbert H) =
      modularUpperCutField M J Ω a (𝓕 ((modularCyclicEmbedding (M := M) J Ω x).compLp F)) := by
  let L := modularCyclicEmbedding (M := M) J Ω x
  exact fourier_intertwines_of_transport L
    ((star (modularCyclicGauge J Ω hsep hcyc x) :
      RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
        RegularCoreHilbert (ModularCyclicSpace M J Ω x)) * regularFrequencyProjection a *
      (modularCyclicGauge J Ω hsep hcyc x :
        RegularCoreHilbert (ModularCyclicSpace M J Ω x) →L[ℂ]
          RegularCoreHilbert (ModularCyclicSpace M J Ω x)))
    (modularCyclicCutField M J Ω x a)
    ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) * regularFrequencyProjection a *
      (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (modularUpperCutField M J Ω a)
    (compLp_regularGaugeFrequency L (modularCyclicGroup J Ω hsep hcyc x)
      (modularStrongGroup J Ω hsep hcyc) (modularCyclicGroup_continuous J Ω hsep hcyc x)
      (modularStrongGroup_continuous J Ω hsep hcyc)
      (modularCyclicEmbedding_group J Ω hsep hcyc x) a)
    (modularCyclicEmbedding_cutField J Ω x a)
    (cyclicGauge_fourier J Ω hsep hcyc x a) F

end

end KadisonKastler

end OAI

import OAI.Analysis.KadisonKastler.ModularGaugeTransport

namespace OAI

/-! # The Fourier gauge identity for the constructed modular group -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform TensorProduct

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularGauge_fourier_tensor (a : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    (𝓕 ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          (scalarLpTensor volume f x)))) : RegularCoreHilbert H) =
      modularUpperCutField M J Ω a (𝓕 (scalarLpTensor volume f x)) := by
  let μ := modularCyclicMeasure (M := M) J Ω x
  let v : ModularCyclicSpace M J Ω x := ContinuousMap.toLp 2 μ ℂ 1
  have hv : modularCyclicEmbedding (M := M) J Ω x v = x :=
    resolventCyclicIsometry_one (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint x
  have ht : (modularCyclicEmbedding (M := M) J Ω x).compLp (scalarLpTensor volume f v) =
      scalarLpTensor volume f x := by
    rw [compLp_scalarLpTensor, hv]
  have h := modularCyclicEmbedding_gauge_fourier J Ω hsep hcyc x a (scalarLpTensor volume f v)
  rw [ht] at h
  exact h

theorem modularGauge_fourier (a : ℝ) (F : RegularCoreHilbert H) :
    (𝓕 ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) F))) : RegularCoreHilbert H) =
      modularUpperCutField M J Ω a (𝓕 F) := by
  let G := regularGauge (modularStrongGroup J Ω hsep hcyc)
    (modularStrongGroup_continuous J Ω hsep hcyc)
  let A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
        regularFrequencyProjection a * (G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
  let B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    (modularUpperCutField M J Ω a).comp
      (Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  change A F = B F
  refine (l2TensorEmbedding_dense volume).induction_on (p := fun F => A F = B F) F ?_ ?_
  · exact isClosed_eq A.continuous B.continuous
  · intro z
    induction z using TensorProduct.inductionOn with
    | tmul f x => exact modularGauge_fourier_tensor J Ω hsep hcyc a f x
    | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

theorem modularGauge_identity (a : ℝ) :
    (star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      regularFrequencyProjection a *
      (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (Lp.fourierTransformₗᵢ ℝ H).symm.conjStarAlgEquiv (modularUpperCutField M J Ω a) := by
  exact linearIsometryEquiv_conjugate_of_intertwines (Lp.fourierTransformₗᵢ ℝ H) _ _
    (modularGauge_fourier J Ω hsep hcyc a)

end

end KadisonKastler

end OAI

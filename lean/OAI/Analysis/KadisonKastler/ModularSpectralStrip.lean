import OAI.Analysis.KadisonKastler.ModularStripIntegral
import OAI.Analysis.KadisonKastler.ModularCyclicPhase

namespace OAI

/-! # Analytic strips for matrix coefficients of the graph resolvent -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def modularSpectralCoefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω X Y : H) :
    spectrum ℝ (graphResolvent M J Ω 1) → ℂ :=
  fun s => star (((resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint Y).toContinuousLinearMap.adjoint X) s)

theorem modularSpectralCoefficient_integrable (J : H ≃ₗᵢ⋆[ℂ] H) (Ω X Y : H) :
    Integrable (modularSpectralCoefficient (M := M) J Ω X Y)
      (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint Y) := by
  exact (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    (Lp.memLp ((resolventCyclicIsometry (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint Y).toContinuousLinearMap.adjoint X)).star)

def modularSpectralStrip (J : H ≃ₗᵢ⋆[ℂ] H) (Ω X Y : H) (z : ℂ) : ℂ :=
  modularStripIntegral
    (resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint Y)
    (fun s => s.val) (modularSpectralCoefficient (M := M) J Ω X Y) z

theorem modularSpectralStrip_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (X Y : H) :
    ContinuousOn (modularSpectralStrip (M := M) J Ω X Y) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ 1} :=
  modularStripIntegral_continuousOn _ _ measurable_subtype_coe _
    (modularSpectralCoefficient_integrable J Ω X Y)
    (graphResolventVectorMeasure_interior J Ω hsep hcyc Y)

theorem modularSpectralStrip_differentiableOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (X Y : H) :
    DifferentiableOn ℂ (modularSpectralStrip (M := M) J Ω X Y) {z : ℂ | 0 < z.im ∧ z.im < 1} :=
  modularStripIntegral_differentiableOn _ _ measurable_subtype_coe _
    (modularSpectralCoefficient_integrable J Ω X Y)
    (graphResolventVectorMeasure_interior J Ω hsep hcyc Y)

theorem modularSpectralStrip_bounded (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (X Y : H) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 →
      ‖modularSpectralStrip (M := M) J Ω X Y z‖ ≤ C := by
  refine ⟨∫ s, ‖modularSpectralCoefficient (M := M) J Ω X Y s‖
    ∂resolventVectorMeasure (graphResolvent M J Ω 1) (graphResolvent_positive J Ω 1).isSelfAdjoint Y,
    fun z hz0 hz1 => ?_⟩
  exact modularStripIntegral_bound _ _ _
    (modularSpectralCoefficient_integrable J Ω X Y)
    (graphResolventVectorMeasure_interior J Ω hsep hcyc Y) ⟨hz0, hz1⟩

end

end KadisonKastler

end OAI

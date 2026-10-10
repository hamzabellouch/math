import OAI.Analysis.KadisonKastler.WeightedStripContinuous
import OAI.Analysis.KadisonKastler.GraphResolventFunctionalCalculus
import OAI.Analysis.KadisonKastler.ResolventContinuousCalculus

namespace OAI

/-! # The bounded holomorphic modular strip on the original space -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def resolventContinuousCalculusLinear (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    C(spectrum ℝ R, ℂ) →L[ℂ] (H →L[ℂ] H) :=
  (resolventContinuousCalculus R hR).toAlgHom.toLinearMap.mkContinuous 1
    (fun f => by change ‖resolventContinuousCalculus R hR f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using
      NonUnitalStarAlgHom.norm_apply_le (resolventContinuousCalculus R hR) f)

def resolventRealCoordinate (R : H →L[ℂ] H) : C(spectrum ℝ R, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def weightedStripOperator (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (z : ℂ) : H →L[ℂ] H :=
  resolventContinuousCalculus (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint
    (weightedStripContinuous (resolventRealCoordinate (graphResolvent M J Ω 1)) z)

theorem weightedStripOperator_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    ContinuousOn (weightedStripOperator (M := M) J Ω) {z : ℂ | |z.re| < 1} :=
  (resolventContinuousCalculusLinear (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint).continuous.comp_continuousOn
      (weightedStripContinuous_continuousOn _)

theorem weightedStripOperator_differentiableOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    DifferentiableOn ℂ (weightedStripOperator (M := M) J Ω) {z : ℂ | |z.re| < 1} :=
  (resolventContinuousCalculusLinear (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint).differentiable.comp_differentiableOn
      (weightedStripContinuous_differentiableOn _)

theorem weightedStripOperator_norm_le (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {z : ℂ} (hz : |z.re| ≤ 1 / 2) : ‖weightedStripOperator (M := M) J Ω z‖ ≤ 1 := by
  apply (NonUnitalStarAlgHom.norm_apply_le _ _).trans
  exact weightedStripContinuous_norm_le _
    (fun s => graphResolvent_spectrum_bounds J Ω s.property) hz

end

end KadisonKastler

end OAI

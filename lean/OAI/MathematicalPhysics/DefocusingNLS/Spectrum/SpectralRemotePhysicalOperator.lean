import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteLeadingSymbol

namespace OAI

/-! Separation of the actual Euler eigenpair system into its leading and bounded parts. -/

namespace DefocusingNLS

noncomputable def spectralRemotePositionPlus : SpectralRemoteSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))
noncomputable def spectralRemotePositionMinus : SpectralRemoteSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ))
noncomputable def spectralRemoteVelocityPlus : SpectralRemoteSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) (ℂ × ℂ))
noncomputable def spectralRemoteVelocityMinus : SpectralRemoteSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ (ℂ × ℂ) (ℂ × ℂ))

noncomputable def spectralRemoteBoundedOperator (dp dm cp cm : ℂ) : SpectralRemoteOperator :=
  ((0 : SpectralRemoteSpace →L[ℂ] ℂ).prod
    ((-12 : ℂ) • spectralRemoteVelocityPlus + dp • spectralRemotePositionPlus +
      cp • spectralRemotePositionMinus)).prod
  ((0 : SpectralRemoteSpace →L[ℂ] ℂ).prod
    ((-12 : ℂ) • spectralRemoteVelocityMinus + dm • spectralRemotePositionMinus +
      cm • spectralRemotePositionPlus))

theorem spectralRemoteBoundedOperator_apply (dp dm cp cm : ℂ) (u : SpectralRemoteSpace) :
    spectralRemoteBoundedOperator dp dm cp cm u =
      ((0,-12*u.1.2+dp*u.1.1+cp*u.2.1),(0,-12*u.2.2+dm*u.2.1+cm*u.1.1)) := rfl

noncomputable def spectralRemotePhysicalBounded (a b sigma : ℝ) (D C : ℂ) : SpectralRemoteOperator :=
  spectralRemoteBoundedOperator (-(b : ℂ)-Complex.I*((a : ℂ)+(sigma : ℂ))+D)
    (-(b : ℂ)+Complex.I*((a : ℂ)+(sigma : ℂ))+star D) C (star C)

theorem spectralRemoteEulerField_operator (a b sigma omega eta : ℝ) (D C : ℂ) (t : ℝ)
    (u : SpectralRemoteSpace) :
    spectralRemoteEulerField a b sigma omega eta D C t u =
      ((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading
        (spectralRemoteLeadingCoefficient (fun _ => omega) (fun _ => eta) 0 t) +
        spectralRemotePhysicalBounded a b sigma D C) u := by
  simp only [spectralRemoteEulerField,spectralRemoteEulerChannelField,
    spectralRemoteLeadingCoefficient,spectralRemotePhysicalLeading,
    ContinuousLinearMap.coe_prodMap',add_apply,smul_apply,
    spectralRemotePhysicalBounded,spectralRemoteBoundedOperator_apply]
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul]
  all_goals
    dsimp only [Prod.map]
    simp only [spectralRemoteLeadingPart_apply,homogeneousSpectralLocalizationRemoteField]
    norm_num

end DefocusingNLS

end OAI

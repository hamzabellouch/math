import OAI.Analysis.KadisonKastler.ModularLocalizedPackets
import OAI.Analysis.KadisonKastler.ScalarPacketCompression

namespace OAI

/-! # Integrated vector-state coefficients of modular Fourier packets -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_regular_vector_coefficient (F : RegularCoreHilbert H) (T : H →L[ℂ] H) :
    Integrable (fun s => inner ℂ (F s) (T (F s))) volume := by
  apply (L2.integrable_inner (𝕜:=ℂ) F (regularConstantHom volume T F)).congr
  filter_upwards [regularConstantHom_apply_ae (volume : Measure ℝ) T F] with s hs
  exact congrArg (inner ℂ (F s)) hs

theorem integral_regular_vector_coefficient (F : RegularCoreHilbert H) (T : H →L[ℂ] H) :
    (∫ s : ℝ, inner ℂ (F s) (T (F s)))=inner ℂ F (regularConstantHom volume T F) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularConstantHom_apply_ae (volume : Measure ℝ) T F] with s hs
  exact (congrArg (inner ℂ (F s)) hs).symm

variable {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem fourierPacket_coefficient
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    (∫ s : ℝ, inner ℂ (S.fourierPacket φ ξ s) (T (S.fourierPacket φ ξ s)))=
      inner ℂ ξ (scalarPacketAverage S.group S.continuous φ hφ T ξ) := by
  rw [integral_regular_vector_coefficient]
  let F := regularGaugedPacket S.group S.continuous φ ξ
  let e := Lp.fourierTransformₗᵢ ℝ H
  have he : regularConstantHom volume T (e F)=e (regularConstantHom volume T F) :=
    (fourier_compLp T F).symm
  change inner ℂ (e F) (regularConstantHom volume T (e F))=_
  rw [he,e.inner_map_map]
  exact regularGaugedPacket_coefficient S.group S.continuous φ hφ T ξ

theorem fourierPacket_coefficient_re
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    (∫ s : ℝ, (inner ℂ (S.fourierPacket φ ξ s) (T (S.fourierPacket φ ξ s))).re)=
      (inner ℂ ξ (scalarPacketAverage S.group S.continuous φ hφ T ξ)).re := by
  calc
    _ = (∫ s : ℝ, inner ℂ (S.fourierPacket φ ξ s) (T (S.fourierPacket φ ξ s))).re :=
      integral_re (𝕜:=ℂ) (integrable_regular_vector_coefficient _ _)
    _ = _ := congrArg Complex.re (S.fourierPacket_coefficient φ hφ T ξ)

end ModularSpectralResolution

end

end KadisonKastler

end OAI

import OAI.Analysis.KadisonKastler.ModularProductState
import OAI.Analysis.KadisonKastler.RegularCommutantPackets
import OAI.Analysis.KadisonKastler.L2Intertwining
import OAI.Analysis.KadisonKastler.FrequencyPacketTensor
import OAI.Analysis.KadisonKastler.RegularPacketLocalization

namespace OAI

/-! # Fourier packets localized by the modular spectral cuts

The already constructed Fourier gauge identity transports bounded scalar
frequency windows to short modular spectral intervals, fiber by fiber.
The norm identity gives the total weight of the resulting vector states.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

def fourierPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) : RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H) (regularGaugedPacket S.group S.continuous φ ξ)

theorem norm_fourierPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖S.fourierPacket φ ξ‖=‖φ‖*‖ξ‖ := by
  rw [fourierPacket,LinearIsometryEquiv.norm_map,norm_regularGaugedPacket_apply]

theorem fourierPacket_cut (a : ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularFieldOperator volume (fun s => S.upperCut (a-2*Real.pi*s))
      (S.measurable a) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
      (S.fourierPacket φ ξ)=S.fourierPacket (regularFrequencyProjection a φ) ξ := by
  let G := regularGauge S.group S.continuous
  let e := Lp.fourierTransformₗᵢ ℝ H
  let x := regularTensorVector φ ξ
  let A := regularFieldOperator volume (fun s => S.upperCut (a-2*Real.pi*s))
    (S.measurable a) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
  have hG : (G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x)=x :=
    congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => T x)
      (Unitary.mul_star_self_of_mem G.property)
  have h := congrArg
    (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      e (T ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x)))
    (S.gauge_identity a)
  change e ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularFrequencyProjection a ((G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x))))=
    e (e.symm (A (e ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x)))) at h
  rw [hG,e.apply_symm_apply] at h
  have ht : regularFrequencyProjection a x=regularTensorVector (regularFrequencyProjection a φ) ξ := by
    change regularFrequencyProjection a (scalarLpTensor volume φ ξ)=
      scalarLpTensor volume (regularFrequencyProjection a φ) ξ
    exact (compLp_regularFrequencyProjection (ContinuousLinearMap.toSpanSingleton ℂ ξ) a φ).symm
  rw [ht] at h
  exact h.symm

theorem fourierPacket_lower_support (a : ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hφ : regularFrequencyProjection a φ=φ) (ξ : H) :
    ∀ᵐ s : ℝ, S.upperCut (a-2*Real.pi*s) (S.fourierPacket φ ξ s)=S.fourierPacket φ ξ s := by
  have h := regularFieldOperator_represents volume (fun s => S.upperCut (a-2*Real.pi*s))
    (S.measurable a) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
    (S.fourierPacket φ ξ)
  rw [S.fourierPacket_cut,hφ] at h
  exact h.symm

theorem fourierPacket_upper_support (b : ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hφ : regularFrequencyProjection b φ=0) (ξ : H) :
    ∀ᵐ s : ℝ, S.upperCut (b-2*Real.pi*s) (S.fourierPacket φ ξ s)=0 := by
  have h := regularFieldOperator_represents volume (fun s => S.upperCut (b-2*Real.pi*s))
    (S.measurable b) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
    (S.fourierPacket φ ξ)
  have hz : S.fourierPacket (0 : Lp ℂ 2 (volume : Measure ℝ)) ξ=0 := by
    simp [fourierPacket,regularGaugedPacket]
  rw [S.fourierPacket_cut,hφ,hz] at h
  filter_upwards [h,Lp.coeFn_zero (E := H) (p := 2) (μ := (volume : Measure ℝ))] with s hs hz
  exact hs.symm.trans hz

theorem fourierPacket_mass (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    (∫ s : ℝ, ‖S.fourierPacket φ ξ s‖^2)=‖φ‖^2*‖ξ‖^2 := by
  rw [regular_integral_norm_sq,S.norm_fourierPacket,mul_pow]

end ModularSpectralResolution

end

end KadisonKastler

end OAI

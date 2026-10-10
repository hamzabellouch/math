import OAI.Analysis.KadisonKastler.RegularActionSpectral
import OAI.Analysis.KadisonKastler.L2FourierNaturality

namespace OAI

/-! # Spectral action on the packets of an invariant vector -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_regularTensorVector (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    (Lp.fourierTransformₗᵢ ℝ H) (regularTensorVector φ x) =
      regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ) φ) x :=
  fourier_scalarLpTensor φ x

theorem regularFrequencyPacket_eq_tensor (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularFrequencyPacket φ x =
      regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ).symm φ) x := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  rw [regularFrequencyPacket, LinearIsometryEquiv.apply_symm_apply,
    fourier_regularTensorVector, LinearIsometryEquiv.apply_symm_apply]

theorem regularConstantHom_frequencyPacket (a : H →L[ℂ] H)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularConstantHom volume a (regularFrequencyPacket φ x) =
      regularFrequencyPacket φ (a x) := by
  rw [regularFrequencyPacket_eq_tensor, regularConstantHom_tensorVector,
    regularFrequencyPacket_eq_tensor]

omit [CompleteSpace H] in
theorem regularScalarMultiplier_tensor (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) (ψ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularScalarMultiplier φ hφ C hC (regularTensorVector ψ x) =
      regularTensorVector (regularScalarMultiplier φ hφ C hC ψ) x := by
  apply Lp.ext
  filter_upwards [regularScalarMultiplier_apply_ae φ hφ C hC (regularTensorVector ψ x),
    regularTensorVector_apply_ae ψ x,
    regularTensorVector_apply_ae (regularScalarMultiplier φ hφ C hC ψ) x,
    regularScalarMultiplier_apply_ae φ hφ C hC ψ] with t hm hψ ht hs
  rw [hm, hψ, ht, hs, smul_smul]
  rfl

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)

include hΩ in
theorem regularGauge_frequencyPacket_fixed (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyPacket ψ Ω) = regularFrequencyPacket ψ Ω := by
  rw [regularFrequencyPacket_eq_tensor]
  apply Lp.ext
  filter_upwards [regularGauge_apply_ae U hU
      (regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ψ) Ω),
    regularTensorVector_apply_ae ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ψ) Ω]
      with t hg ht
  rw [hg, ht, map_smul, hΩ]

include hΩ in
theorem regularGauge_star_frequencyPacket_fixed (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyPacket ψ Ω) = regularFrequencyPacket ψ Ω := by
  have h := congrArg (fun f => (star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
    (regularGauge_frequencyPacket_fixed U hU Ω hΩ ψ)
  have he := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      A (regularFrequencyPacket ψ Ω))
    (Unitary.star_mul_self_of_mem (regularGauge U hU).property)
  exact h.symm.trans he

include hΩ in
theorem regularActionMultiplier_packet (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    regularActionMultiplier U hU φ hφ C hC (regularFrequencyPacket ψ Ω) =
      regularFrequencyPacket (regularScalarMultiplier φ hφ C hC ψ) Ω := by
  simp only [regularActionMultiplier, unitaryConj, mul_apply_eq_comp,
    Unitary.coe_star, star_star, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  rw [regularGauge_frequencyPacket_fixed U hU Ω hΩ]
  unfold regularFrequencyPacket
  rw [LinearIsometryEquiv.apply_symm_apply, regularScalarMultiplier_tensor]
  exact regularGauge_star_frequencyPacket_fixed U hU Ω hΩ _

end

end KadisonKastler

end OAI

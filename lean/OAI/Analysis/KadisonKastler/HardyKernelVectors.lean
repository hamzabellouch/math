import OAI.Analysis.KadisonKastler.HardyKernelShift
import OAI.Analysis.KadisonKastler.CharacterPacketTotality
import OAI.Analysis.KadisonKastler.RegularActionPackets

namespace OAI

/-! # Reproducing-kernel vectors and their character tests -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyProjection_zero_tensor (φ : RegularCoreHilbert ℂ) (x : H) :
    regularFrequencyProjection 0 (regularTensorVector φ x) =
      regularTensorVector (regularFrequencyProjection 0 φ) x := by
  have hn (ψ : RegularCoreHilbert ℂ) :
      FourierTransform.fourier (regularTensorVector ψ x) =
        regularTensorVector (FourierTransform.fourier ψ) x :=
    fourier_regularTensorVector ψ x
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change FourierTransform.fourier (regularFrequencyProjection 0 (regularTensorVector φ x)) =
    FourierTransform.fourier (regularTensorVector (regularFrequencyProjection 0 φ) x)
  rw [fourier_frequencyProjection_zero, hn,
    regularIndicatorProjection_tensor, hn,
    fourier_frequencyProjection_zero]

theorem regularCharacter_tensor (a : ℝ) (φ : RegularCoreHilbert ℂ) (x : H) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularTensorVector φ x) =
    regularTensorVector
      ((regularCharacterUnitary (H := ℂ) a : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) φ) x := by
  apply Lp.ext
  filter_upwards [regularCharacterUnitary_apply_ae a (regularTensorVector φ x),
    regularTensorVector_apply_ae φ x,
    regularTensorVector_apply_ae ((regularCharacterUnitary (H := ℂ) a :
      RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) φ) x,
    regularCharacterUnitary_apply_ae a φ] with s h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_smul]
  rfl

theorem hardyKernelInclusion_positive (z : ℂ) (hz : 0 < z.re) (x : H) :
    regularFrequencyProjection 0 (hardyKernelInclusion z hz x) =
      hardyKernelInclusion z hz x := by
  change regularFrequencyProjection 0 (regularTensorVector (hardyUnitKernel z hz) x) = _
  rw [regularFrequencyProjection_zero_tensor, hardyUnitKernel_positive]
  rfl

theorem hardyUnitKernel_backward_shift (z : ℂ) (hz : 0 < z.re)
    {b : ℝ} (hb : 0 ≤ b) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := ℂ) (2 * Real.pi * (-b)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) (hardyUnitKernel z hz)) =
        Complex.exp (-z * b) • hardyUnitKernel z hz := by
  simp only [hardyUnitKernel, map_smul, hardyReproducingKernel_backward_shift z hz hb,
    smul_smul]
  congr 1
  ring

theorem hardyKernelInclusion_backward_shift (z : ℂ) (hz : 0 < z.re)
    {b : ℝ} (hb : 0 ≤ b) (x : H) :
    regularFrequencyProjection 0
      ((regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
        Complex.exp (-z * b) • hardyKernelInclusion z hz x := by
  change regularFrequencyProjection 0
    ((regularCharacterUnitary (H := H) (2 * Real.pi * (-b)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularTensorVector (hardyUnitKernel z hz) x)) = _
  rw [regularCharacter_tensor, regularFrequencyProjection_zero_tensor,
    hardyUnitKernel_backward_shift z hz hb]
  rw [map_smul]
  rfl

theorem hardyKernelInclusion_adjoint_self (z : ℂ) (hz : 0 < z.re) :
    (hardyKernelInclusion (H := H) z hz).toContinuousLinearMap.adjoint.comp
      (hardyKernelInclusion z hz).toContinuousLinearMap = ContinuousLinearMap.id ℂ H := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((hardyKernelInclusion z hz).toContinuousLinearMap.adjoint
    (hardyKernelInclusion z hz x)) = inner ℂ y x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (hardyKernelInclusion z hz).inner_map_map y x

theorem hardyUnitKernel_ne_zero_ae (z : ℂ) (hz : 0 < z.re) :
    ∀ᵐ s : ℝ, hardyUnitKernel z hz s ≠ 0 := by
  filter_upwards [hardyUnitKernel_density hz] with s hs
  have hp : 0 < realPoissonKernel (z.im / (2 * Real.pi)) (z.re / (2 * Real.pi)) s := by
    unfold realPoissonKernel
    positivity
  intro hzero
  rw [hzero, norm_zero, zero_pow (by decide)] at hs
  linarith

/-- Character-kernel vectors determine continuous operators on the regular space. -/
theorem hardyKernelInclusion_ext (z : ℂ) (hz : 0 < z.re)
    {A B : RegularCoreHilbert H →L[ℂ] H}
    (he : ∀ s : ℝ, ∀ x : H,
      A ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x)) =
      B ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x))) :
    A = B := by
  have ha : A.adjoint = B.adjoint := by
    apply ContinuousLinearMap.ext
    intro y
    apply sub_eq_zero.mp
    apply eq_zero_of_inner_character_packets (hardyUnitKernel z hz) (hardyUnitKernel_ne_zero_ae z hz)
    intro s x
    rw [inner_sub_right, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (A ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x))) y -
      inner ℂ (B ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (hardyKernelInclusion z hz x))) y = 0
    rw [he, sub_self]
  have h := congrArg ContinuousLinearMap.adjoint ha
  simpa only [ContinuousLinearMap.adjoint_adjoint] using h

end

end KadisonKastler

end OAI

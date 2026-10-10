import OAI.Analysis.LipschitzHilbert.Phase.ScalarBandDiagonal
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBinPairing

namespace OAI

/-! The scalar annular form is the actual time operator applied to the
original vertical cutoff; the test is not projected. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annularScalarMultiplier_eq (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (hl : 0<l) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 (annularBandSymbol psi beta l W center u) f z=
      slopeKernelOperator (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) u
        (schwartzVerticalProjection beta W center f) z := by
  rw [schwartz_frozen_slope_multiplier _
    (scaledTimeKernel_integrable (𝓕⁻ psi : SchwartzMap ℝ ℂ) (𝓕⁻ psi : SchwartzMap ℝ ℂ).integrable
      l hl.ne')]
  have hfour (s : ℝ) : 𝓕 (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) s=psi (l*s) := by
    rw [scaledTimeKernel_fourier _ l hl]
    have heq : (𝓕 (𝓕⁻ psi : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=psi := fourier_fourierInv_eq psi
    exact congrArg (fun q : SchwartzMap ℝ ℂ => q (l*s)) heq
  unfold variableFrequencyMultiplierL1
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [hfour]
  congr 1
  simp only [annularBandSymbol,symbolY,schwartzVerticalProjection_fourier,mul_assoc]

theorem scalarBandForm_eq_kernel (psi beta : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength W center : ℝ) (htop : 0<topLength)
    (u : (ℝ×ℝ) → ℝ) (hum : Measurable u) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    scalarBandForm psi beta N topLength W center u f g=
      ∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
        (schwartzVerticalProjection beta W center f) z*star (g z) ∂planeMeasure := by
  let M := fun j : Fin N => annularBandSymbol psi beta (topLength/(2:ℝ)^j.val) W center u
  have hi (j : Fin N) : Integrable (fun z => variableFrequencyMultiplierL1 (M j) f z*star (g z))
      planeMeasure := by
    apply variableFrequencyMultiplier_pairing_integrable (M j)
      (annularBandSymbol_measurable _ _ _ _ _ u hum)
      (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 beta) _ f g g.integrable
    intro z omega
    dsimp only [M,annularBandSymbol]
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _)
      (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (apply_nonneg _ _)
  change (∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1 (M j) f z*star (g z) ∂planeMeasure)=_
  rw [←integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [slopeKernelOperator_finiteTimeKernel _ N topLength htop,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [annularScalarMultiplier_eq psi beta _ W center (div_pos htop (pow_pos (by norm_num) _))]

end LipschitzHilbert.PacketRepresentation

end

end OAI

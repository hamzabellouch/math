import OAI.Analysis.LipschitzHilbert.Phase.FiniteDiagonalBandL1
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinReconstruction
import OAI.Analysis.LipschitzHilbert.Fourier.FiniteTimeKernelMoment

namespace OAI

/-! The annular symbol with the enlarged bin plateau is exactly the time
kernel acting on the true bin projection. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annularBinMultiplier_eq (psi : SchwartzMap ℝ ℂ) (l W center : ℝ) (hl : 0<l)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    variableFrequencyMultiplierL1 (annularBandSymbol psi verticalBinPlateau l W center u)
      (schwartzVerticalProjection verticalBinProfile W center f) z=
      slopeKernelOperator (scaledTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) l) u
        (schwartzVerticalProjection verticalBinProfile W center f) z := by
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
  simp only [annularBandSymbol,symbolY,schwartzVerticalProjection_fourier]
  rw [mul_assoc,←mul_assoc (verticalBinPlateau _) (verticalBinProfile _),verticalBinPlateau_mul_profile]

theorem slopeKernelOperator_finiteTimeKernel (k : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength : ℝ) (htop : 0<topLength) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator (finiteTimeKernel k N topLength) u f z=
      ∑ j : Fin N, slopeKernelOperator (scaledTimeKernel k (topLength/(2:ℝ)^j.val)) u f z := by
  have hi (j : Fin N) : Integrable (fun t =>
      scaledTimeKernel k (topLength/(2:ℝ)^j.val) t*f (z.1-t,z.2-t*u z)) := by
    have hk := scaledTimeKernel_integrable k k.integrable (topLength/(2:ℝ)^j.val)
      (ne_of_gt (div_pos htop (pow_pos (by norm_num) _)))
    apply (hk.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    · exact hk.aestronglyMeasurable.mul (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f _) (norm_nonneg _)
  unfold slopeKernelOperator finiteTimeKernel
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ (fun j _ => hi j)

end LipschitzHilbert.PacketRepresentation

end

end OAI

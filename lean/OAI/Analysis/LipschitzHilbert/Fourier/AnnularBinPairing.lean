import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBinMultiplier
import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeOperator
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBandL1

namespace OAI

/-! On the original narrow horizontal strip, the actual projected time
pairing equals the finite annular-symbol pairing without a time cutoff. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annularBin_pairing (psi : SchwartzMap ℝ ℂ) (N : ℕ) (topLength W center : ℝ)
    (htop : 0<topLength) (hW : 0<W) (u : (ℝ×ℝ) → ℝ) (hum : Measurable u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0) :
    (∫ z, shortSlopeOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
      (schwartzVerticalProjection verticalBinProfile W center f) z*
        star (schwartzVerticalProjection verticalBinProfile W center g z) ∂planeMeasure)=
      ∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi verticalBinPlateau (topLength/(2:ℝ)^j.val) W center u)
        (schwartzVerticalProjection verticalBinProfile W center f) z*
          star (schwartzVerticalProjection verticalBinProfile W center g z) ∂planeMeasure := by
  let F := schwartzVerticalProjection verticalBinProfile W center f
  let G := schwartzVerticalProjection verticalBinProfile W center g
  let T := finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength
  let M := fun j : Fin N => annularBandSymbol psi verticalBinPlateau
    (topLength/(2:ℝ)^j.val) W center u
  have hlen (j : Fin N) : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  have hFp : ∀ z, z.1∉Icc l r → F z=0 := by
    intro z hz
    rw [schwartzVerticalProjection_eq_convolution _ W center hW]
    exact verticalConvolution_horizontal_support _ f (Icc l r) hf z hz
  have hGp : ∀ z, z.1∉Icc l r → G z=0 := by
    intro z hz
    rw [schwartzVerticalProjection_eq_convolution _ W center hW]
    exact verticalConvolution_horizontal_support _ g (Icc l r) hg z hz
  have hi (j : Fin N) : Integrable (fun z => variableFrequencyMultiplierL1 (M j) F z*star (G z))
      planeMeasure := by
    apply variableFrequencyMultiplier_pairing_integrable (M j)
      (annularBandSymbol_measurable _ _ _ _ _ u hum)
      (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 verticalBinPlateau)
      _ F G G.integrable
    intro z omega
    dsimp only [M,annularBandSymbol]
    rw [norm_mul]
    exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _)
      (SchwartzMap.norm_le_seminorm ℝ verticalBinPlateau _) (norm_nonneg _)
      (apply_nonneg _ _)
  have heq (z : ℝ×ℝ) : slopeKernelOperator T u F z=
      ∑ j : Fin N, variableFrequencyMultiplierL1 (M j) F z := by
    rw [slopeKernelOperator_finiteTimeKernel _ N topLength htop]
    exact Finset.sum_congr rfl (fun j _ => (annularBinMultiplier_eq psi
      (topLength/(2:ℝ)^j.val) W center (hlen j) u f z).symm)
  calc
    _ = ∫ z, slopeKernelOperator T u F z*star (G z) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall fun z =>
        shortSlopeOperator_pairing_eq T u F G l r hwidth hFp hGp z)
    _ = ∫ z, ∑ j : Fin N, variableFrequencyMultiplierL1 (M j) F z*star (G z) ∂planeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [heq,Finset.sum_mul]
    _ = _ := integral_finsetSum _ (fun j _ => hi j)

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.ActualBinPairing
import OAI.Analysis.LipschitzHilbert.Fourier.AnnularBinPairing
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinVector

namespace OAI

/-! Exact identification of the physical localized operator pairing with
the finite diagonal form used by the high-disparity estimate. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem actualBand_pairing_eq_diagonal (psi : SchwartzMap ℝ ℂ) (N : ℕ)
    (topLength w W c C : ℝ) (htop : 0<topLength) (hw : 0<w) (hW : 0<W)
    (hc : 0<c) (hC : 0<C) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f g : SchwartzMap (ℝ×ℝ) ℂ)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C)
    (l r : ℝ) (hwidth : r-l≤1/4)
    (hf : ∀ z, z.1∉Icc l r → f z=0) (hg : ∀ z, z.1∉Icc l r → g z=0) :
    let J := ⌈C*W/w⌉₊
    let I := verticalBinLabels J w W c C
    (∫ z, shortSlopeOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
      u f z*star (g z) ∂planeMeasure)=
      finiteDiagonalBandL1 (N:=N) psi verticalBinPlateau topLength W
        (fun n : I => verticalBinCenter J W n) u
        (fun n z => verticalConvolution
          (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)) f z)
        (verticalBinVector I J W g)-
      ∫ z, totalProjectedBinError (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C u f z*
        star (g z) ∂planeMeasure := by
  intro J I
  rw [actualBin_pairing (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength w W c C htop hw hW hc hC u hu f g hband]
  congr 1
  calc
    _ = ∑ n : I, ∑ j : Fin N, ∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi verticalBinPlateau (topLength/(2:ℝ)^j.val) W
          (verticalBinCenter J W n) u)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f) z*
          star (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g z)
            ∂planeMeasure := by
      apply Finset.sum_congr rfl
      intro n _
      exact annularBin_pairing psi N topLength W (verticalBinCenter J W n) htop hW u
        hu.continuous.measurable f g l r hwidth hf hg
    _ = ∑ j : Fin N, ∑ n : I, ∫ z, variableFrequencyMultiplierL1
        (annularBandSymbol psi verticalBinPlateau (topLength/(2:ℝ)^j.val) W
          (verticalBinCenter J W n) u)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f) z*
          star (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g z)
            ∂planeMeasure := Finset.sum_comm
    _ = _ := by
      unfold finiteDiagonalBandL1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro n _
      have hpf : (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) f :
          (ℝ×ℝ) → ℂ)=verticalConvolution
            (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)) f :=
        funext (schwartzVerticalProjection_eq_convolution _ W _ hW f)
      have hpg : (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter J W n) g :
          (ℝ×ℝ) → ℂ)=verticalConvolution
            (verticalProfileKernel verticalBinProfile W (verticalBinCenter J W n)) g :=
        funext (schwartzVerticalProjection_eq_convolution _ W _ hW g)
      change (∫ z, _*star ((schwartzVerticalProjection verticalBinProfile W
        (verticalBinCenter J W n) g : (ℝ×ℝ) → ℂ) z) ∂planeMeasure)=_
      rw [hpf,hpg]
      rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI

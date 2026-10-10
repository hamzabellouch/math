import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedFrameTerminal
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTerminalResidualBound

namespace OAI

/-! Quantitative terminal transfer error for a bounded oscillatory frame.
The factor multiplying the terminal data tends to zero with the integrated
residual. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectral_bounded_frame_terminal_error
    (R E C c J : ℝ) (hRE : R ≤ E) (hC : 0 ≤ C) (hc : 0 < c)
    (D U q : ℝ → ℂ × ℂ) (V e : ℝ → ℂ) (W : ℂ) (k : ℝ → ℝ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hVc : ContinuousOn V (Icc R E))
    (hec : ContinuousOn e (Icc R E)) (hkc : ContinuousOn k (Icc R E))
    (hk : ∀ t ∈ Icc R E, 0 < k t) (hW : c ≤ ‖W‖)
    (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t) = W)
    (hD : ∀ t ∈ Ioo R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (V t) (q t)+(0,e t*(q t).1)) t)
    (hDb : ∀ t ∈ Icc R E, spectralShellNorm (k t) (D t) ≤ C)
    (hUb : ∀ t ∈ Icc R E, spectralShellNorm (k t) (U t) ≤ C)
    (hJ : (∫ t in R..E, ‖e t‖/(k t)^2) ≤ J) :
    spectralShellNorm (k R)
      (q R - ((spectralScalarWronskian (q E) (U E)/W) • D R +
        (spectralScalarWronskian (D E) (q E)/W) • U R)) ≤
      (2*(2*C^2/c)^2*Real.exp ((2*C^2/c)*J)*J)*spectralShellNorm (k E) (q E) := by
  let A := 2*C^2/c
  let B := (2*A*Real.exp (A*J))*spectralShellNorm (k E) (q E)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := mul_nonneg (by positivity)
    (spectralShellNorm_nonneg (k E) (hk E ⟨hRE,le_rfl⟩).le _)
  have hqbound := spectral_bounded_frame_terminal_bound R E C c J hC hc D U q V e W k
    hDc hUc hqc hVc hec hkc hk hW hdet hD hU hq hDb hUb hJ
  have hkernel (t : ℝ) (ht : t ∈ Icc R E) :
      spectralShellNorm (k R) (spectralScalarTransferKernel D U W R t) ≤ A/k t := by
    have hh := spectralScalarTransferKernel_bound D U W (k R) (k t) C c 0 0 R t
      (hk R ⟨le_rfl,hRE⟩).le (hk t ht) hC hc hW
      (by simpa only [Real.exp_zero,mul_one] using hDb R ⟨le_rfl,hRE⟩)
      (by simpa only [Real.exp_zero,mul_one] using hDb t ht)
      (by simpa only [neg_zero,Real.exp_zero,mul_one] using hUb R ⟨le_rfl,hRE⟩)
      (by simpa only [neg_zero,Real.exp_zero,mul_one] using hUb t ht)
    simpa only [A,sub_self,abs_zero,Real.exp_zero,mul_one,div_div] using hh
  have hb := spectralScalar_terminal_comparison_error R E A B hRE hA hB D U q V e W k
    hDc hUc hqc hec hkc hk (norm_pos_iff.mp (hc.trans_le hW)) hdet hD hU hq hkernel hqbound
  calc
    _ ≤ A*B*(∫ t in R..E, ‖e t‖/(k t)^2) := hb
    _ ≤ A*B*J := mul_le_mul_of_nonneg_left hJ (mul_nonneg hA hB)
    _ = _ := by dsimp only [A,B]; ring

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarTerminalDuhamel

namespace OAI

/-! A terminal comparison error is controlled by the integral of the scaled
residual and a bound for the true Cauchy data. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalar_terminal_residual_bound
    (R E kr A B : ℝ) (hRE : R ≤ E) (hkr : 0 ≤ kr) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (D U q : ℝ → ℂ × ℂ) (W : ℂ) (e : ℝ → ℂ) (k : ℝ → ℝ)
    (hD : ContinuousOn D (Icc R E)) (hU : ContinuousOn U (Icc R E))
    (hq : ContinuousOn q (Icc R E)) (he : ContinuousOn e (Icc R E))
    (hk : ContinuousOn k (Icc R E)) (hk0 : ∀ t ∈ Icc R E, 0 < k t)
    (hkernel : ∀ t ∈ Icc R E,
      spectralShellNorm kr (spectralScalarTransferKernel D U W R t) ≤ A/k t)
    (hqbound : ∀ t ∈ Icc R E, spectralShellNorm (k t) (q t) ≤ B) :
    spectralShellNorm kr
      (∫ t in R..E, (e t*(q t).1) • spectralScalarTransferKernel D U W R t) ≤
      A*B*(∫ t in R..E, ‖e t‖/(k t)^2) := by
  have hK : ContinuousOn (fun t => spectralScalarTransferKernel D U W R t) (Icc R E) :=
    ((hD.fst.div_const W).smul continuousOn_const).sub
      ((hU.fst.div_const W).smul continuousOn_const)
  have hg : ContinuousOn (fun t => A*B*(‖e t‖/(k t)^2)) (Icc R E) :=
    continuousOn_const.mul (he.norm.div (hk.pow 2) (fun t ht => pow_ne_zero _ (hk0 t ht).ne'))
  have hval (t : ℝ) (ht : t ∈ Icc R E) : ‖(q t).1‖ ≤ B/k t :=
    (spectralShellNorm_value (k t) (hk0 t ht) (q t)).trans
      (div_le_div_of_nonneg_right (hqbound t ht) (hk0 t ht).le)
  have hb := spectralShellNorm_integral_bound R E kr hRE hkr
    (fun t => (e t*(q t).1) • spectralScalarTransferKernel D U W R t)
    (fun t => A*B*(‖e t‖/(k t)^2)) ((he.mul hq.fst).smul hK) hg (by
      intro t ht
      have hkt := hk0 t ht
      rw [spectralShellNorm_smul,norm_mul]
      calc
        _ = ‖e t‖*(‖(q t).1‖*spectralShellNorm kr (spectralScalarTransferKernel D U W R t)) := by ring
        _ ≤ ‖e t‖*((B/k t)*(A/k t)) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hval t ht) (hkernel t ht)
            (spectralShellNorm_nonneg kr hkr _) (by positivity)) (norm_nonneg _)
        _ = A*B*(‖e t‖/(k t)^2) := by ring)
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb

theorem spectralScalar_terminal_comparison_error
    (R E A B : ℝ) (hRE : R ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (D U q : ℝ → ℂ × ℂ) (V e : ℝ → ℂ) (W : ℂ) (k : ℝ → ℝ)
    (hDc : ContinuousOn D (Icc R E)) (hUc : ContinuousOn U (Icc R E))
    (hqc : ContinuousOn q (Icc R E)) (hec : ContinuousOn e (Icc R E))
    (hkc : ContinuousOn k (Icc R E)) (hk : ∀ t ∈ Icc R E, 0 < k t)
    (hW : W ≠ 0) (hdet : ∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t) = W)
    (hD : ∀ t ∈ Ioo R E, HasDerivAt D (spectralScalarField (V t) (D t)) t)
    (hU : ∀ t ∈ Ioo R E, HasDerivAt U (spectralScalarField (V t) (U t)) t)
    (hq : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField (V t) (q t)+(0,e t*(q t).1)) t)
    (hkernel : ∀ t ∈ Icc R E,
      spectralShellNorm (k R) (spectralScalarTransferKernel D U W R t) ≤ A/k t)
    (hqbound : ∀ t ∈ Icc R E, spectralShellNorm (k t) (q t) ≤ B) :
    spectralShellNorm (k R)
      (q R - ((spectralScalarWronskian (q E) (U E)/W) • D R +
        (spectralScalarWronskian (D E) (q E)/W) • U R)) ≤
      A*B*(∫ t in R..E, ‖e t‖/(k t)^2) := by
  have hrep := spectralScalar_terminal_representation R E D U q V
    (fun t => e t*(q t).1) W hDc hUc hqc (hec.mul hqc.fst) hW hdet hD hU hq R ⟨le_rfl,hRE⟩
  have herr : q R - ((spectralScalarWronskian (q E) (U E)/W) • D R +
      (spectralScalarWronskian (D E) (q E)/W) • U R) =
      -(∫ t in R..E, (e t*(q t).1) • spectralScalarTransferKernel D U W R t) := by
    rw [hrep]
    abel
  rw [herr,spectralShellNorm_neg]
  exact spectralScalar_terminal_residual_bound R E (k R) A B hRE
    (hk R ⟨le_rfl,hRE⟩).le hA hB D U q W e k hDc hUc hqc hec hkc hk hkernel hqbound

end DefocusingNLS

end OAI

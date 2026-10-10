import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarDuhamel

namespace OAI

/-! A weighted estimate for the actual Duhamel integral, with its same-channel
exponential factor retained for the subsequent Gronwall step. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalarDuhamelIntegral_bound (R r kr : ℝ) (hr : R≤ r) (hk : 0≤ kr)
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (f : ℝ → ℂ) (B : ℝ → ℝ)
    (hD : ContinuousOn D (Icc R r)) (hU : ContinuousOn U (Icc R r))
    (hf : ContinuousOn f (Icc R r)) (hB : ContinuousOn B (Icc R r))
    (hbound : ∀ t ∈ Icc R r, spectralShellNorm kr (spectralScalarTransferKernel D U W r t)≤ B t) :
    spectralShellNorm kr (spectralScalarDuhamelIntegral R D U W f r)≤
      ∫ t in R..r, B t*‖f t‖ := by
  rw [spectralScalarDuhamelIntegral_eq_integral R r hr D U W f hD hU hf]
  have hK : ContinuousOn (fun t => spectralScalarTransferKernel D U W r t) (Icc R r) :=
    ((hD.fst.div_const W).smul continuousOn_const).sub
      ((hU.fst.div_const W).smul continuousOn_const)
  apply spectralShellNorm_integral_bound R r kr hr hk _ _ (hf.smul hK) (hB.mul hf.norm)
  intro t ht
  change spectralShellNorm kr ((f t) • spectralScalarTransferKernel D U W r t)≤ B t*‖f t‖
  rw [spectralShellNorm_smul,mul_comm]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

theorem spectralScalarDuhamelIntegral_residual_bound
    (R r A : ℝ) (hr : R≤ r) (hA : 0≤ A)
    (D U q : ℝ → ℂ × ℂ) (W : ℂ) (e : ℝ → ℂ) (k H : ℝ → ℝ)
    (hD : ContinuousOn D (Icc R r)) (hU : ContinuousOn U (Icc R r))
    (hq : ContinuousOn q (Icc R r)) (he : ContinuousOn e (Icc R r))
    (hk : ContinuousOn k (Icc R r)) (hH : ContinuousOn H (Icc R r))
    (hk0 : ∀ t ∈ Icc R r, 0<k t)
    (hbound : ∀ t ∈ Icc R r,
      spectralShellNorm (k r) (spectralScalarTransferKernel D U W r t)≤
        A/k t*Real.exp (H r-H t)) :
    spectralShellNorm (k r) (spectralScalarDuhamelIntegral R D U W (fun t => e t*(q t).1) r)≤
      ∫ t in R..r, (A*‖e t‖/(k t)^2)*Real.exp (H r-H t)*spectralShellNorm (k t) (q t) := by
  have hkc : ContinuousOn (fun t => A/k t*Real.exp (H r-H t)) (Icc R r) :=
    (continuousOn_const.div hk (fun t ht => (hk0 t ht).ne')).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.sub hH))
  have hb := spectralScalarDuhamelIntegral_bound R r (k r) hr (hk0 r ⟨hr,le_rfl⟩).le
    D U W (fun t => e t*(q t).1) _ hD hU (he.mul hq.fst) hkc hbound
  apply hb.trans
  have hN : ContinuousOn (fun t => spectralShellNorm (k t) (q t)) (Icc R r) :=
    (hk.mul hq.fst.norm).add (hk.inv₀ (fun t ht => (hk0 t ht).ne') |>.mul hq.snd.norm)
  have hright : ContinuousOn
      (fun t => (A*‖e t‖/(k t)^2)*Real.exp (H r-H t)*spectralShellNorm (k t) (q t)) (Icc R r) :=
    (((continuousOn_const.mul he.norm).div (hk.pow 2) (fun t ht => pow_ne_zero _ (hk0 t ht).ne')).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.sub hH))).mul hN
  apply intervalIntegral.integral_mono_on hr
    (ContinuousOn.intervalIntegrable_of_Icc hr (hkc.mul (he.mul hq.fst).norm))
    (ContinuousOn.intervalIntegrable_of_Icc hr hright)
  intro t ht
  dsimp only [Pi.mul_apply]
  have hkt := hk0 t ht
  rw [norm_mul]
  calc
    _ ≤ (A/k t*Real.exp (H r-H t))*(‖e t‖*(spectralShellNorm (k t) (q t)/k t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (spectralShellNorm_value (k t) (hk0 t ht) (q t)) (norm_nonneg _)
    _ = _ := by field_simp

end DefocusingNLS

end OAI

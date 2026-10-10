import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! Integration in the scaled value/derivative norm on a finite interval. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralShellNorm_integral_le (a b k : ℝ) (hab : a≤ b) (hk : 0≤ k)
    (F : ℝ → ℂ × ℂ) (hF : ContinuousOn F (Icc a b)) :
    spectralShellNorm k (∫ t in a..b, F t)≤∫ t in a..b, spectralShellNorm k (F t) := by
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hF
  have hif := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hF.fst.norm
  have hig := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hF.snd.norm
  have hf := (ContinuousLinearMap.fst ℝ ℂ ℂ).intervalIntegral_comp_comm hi
  have hg := (ContinuousLinearMap.snd ℝ ℂ ℂ).intervalIntegral_comp_comm hi
  change (∫ t in a..b, (F t).1)=(∫ t in a..b, F t).1 at hf
  change (∫ t in a..b, (F t).2)=(∫ t in a..b, F t).2 at hg
  dsimp only [spectralShellNorm]
  rw [← hf,← hg,intervalIntegral.integral_add (hif.const_mul k) (hig.const_mul k⁻¹),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab) hk)
    (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm hab) (inv_nonneg.mpr hk))

theorem spectralShellNorm_integral_bound (a b k : ℝ) (hab : a≤ b) (hk : 0≤ k)
    (F : ℝ → ℂ × ℂ) (B : ℝ → ℝ)
    (hF : ContinuousOn F (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ t ∈ Icc a b, spectralShellNorm k (F t)≤ B t) :
    spectralShellNorm k (∫ t in a..b, F t)≤∫ t in a..b, B t := by
  apply (spectralShellNorm_integral_le a b k hab hk F hF).trans
  have hN : ContinuousOn (fun t => spectralShellNorm k (F t)) (Icc a b) :=
    (continuousOn_const.mul hF.fst.norm).add (continuousOn_const.mul hF.snd.norm)
  exact intervalIntegral.integral_mono_on hab
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hN)
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hB) hbound

end DefocusingNLS

end OAI

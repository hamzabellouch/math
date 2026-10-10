import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreenIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellIntegral

namespace OAI

/-! An operator bound for the actual Green integral from its two scalar action bounds. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralScalarGreenIntegral_shell_bound
    (R E r k : ℝ) (hr : r ∈ Icc R E) (hk : 0≤ k)
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (f : ℝ → ℂ) (B : ℝ → ℝ)
    (hD : ContinuousOn D (Icc R E)) (hU : ContinuousOn U (Icc R E))
    (hf : ContinuousOn f (Icc R E)) (hB : ContinuousOn B (Icc R E))
    (hleft : ∀ t ∈ Icc R r,
      spectralShellNorm k (((D t).1/W) • U r)≤ B t)
    (hright : ∀ t ∈ Icc r E,
      spectralShellNorm k (((U t).1/W) • D r)≤ B t) :
    spectralShellNorm k (spectralScalarGreenIntegral R E D U W f r)≤
      ∫ t in R..E, B t*‖f t‖ := by
  let FL := fun t => f t • (((D t).1/W) • U r)
  let FR := fun t => f t • (((U t).1/W) • D r)
  have hFL : ContinuousOn FL (Icc R E) := by dsimp only [FL]; fun_prop
  have hFR : ContinuousOn FR (Icc R E) := by dsimp only [FR]; fun_prop
  have hBL (t : ℝ) (ht : t ∈ Icc R r) : spectralShellNorm k (FL t)≤ B t*‖f t‖ := by
    dsimp only [FL]
    rw [spectralShellNorm_smul]
    exact (mul_le_mul_of_nonneg_left (hleft t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hBR (t : ℝ) (ht : t ∈ Icc r E) : spectralShellNorm k (FR t)≤ B t*‖f t‖ := by
    dsimp only [FR]
    rw [spectralShellNorm_smul]
    exact (mul_le_mul_of_nonneg_left (hright t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have heL : (∫ t in R..r, (D t).1*f t/W) • U r=∫ t in R..r, FL t := by
    rw [← intervalIntegral.integral_smul_const]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [FL]
    rw [smul_smul]
    congr 1
    ring
  have heR : (∫ t in r..E, (U t).1*f t/W) • D r=∫ t in r..E, FR t := by
    rw [← intervalIntegral.integral_smul_const]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [FR]
    rw [smul_smul]
    congr 1
    ring
  have hbc : ContinuousOn (fun t => B t*‖f t‖) (Icc R E) := hB.mul hf.norm
  have hsubL : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
  have hsubR : Icc r E ⊆ Icc R E := Icc_subset_Icc hr.1 le_rfl
  calc
    _ = spectralShellNorm k ((∫ t in R..r, FL t)+(∫ t in r..E, FR t)) := by
      rw [spectralScalarGreenIntegral,heL,heR]
    _ ≤ spectralShellNorm k (∫ t in R..r, FL t)+spectralShellNorm k (∫ t in r..E, FR t) :=
      spectralShellNorm_add_le k hk _ _
    _ ≤ (∫ t in R..r, B t*‖f t‖)+(∫ t in r..E, B t*‖f t‖) :=
      add_le_add
        (spectralShellNorm_integral_bound R r k hr.1 hk FL _ (hFL.mono hsubL) (hbc.mono hsubL) hBL)
        (spectralShellNorm_integral_bound r E k hr.2 hk FR _ (hFR.mono hsubR) (hbc.mono hsubR) hBR)
    _ = _ := intervalIntegral.integral_add_adjacent_intervals
      (ContinuousOn.intervalIntegrable_of_Icc hr.1 (hbc.mono hsubL))
      (ContinuousOn.intervalIntegrable_of_Icc hr.2 (hbc.mono hsubR))

end DefocusingNLS

end OAI

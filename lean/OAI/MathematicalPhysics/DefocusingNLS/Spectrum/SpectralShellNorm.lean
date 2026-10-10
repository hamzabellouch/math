import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarGreen

namespace OAI

/-! The scaled value/derivative norm in the fixed-shell transfer estimate.
Here `k` is the square root of the regularized frequency magnitude. -/

namespace DefocusingNLS

noncomputable def spectralShellNorm (k : ℝ) (u : ℂ × ℂ) : ℝ :=
  k * ‖u.1‖ + k⁻¹ * ‖u.2‖

theorem spectralShellNorm_nonneg (k : ℝ) (hk : 0≤ k) (u : ℂ × ℂ) :
    0≤ spectralShellNorm k u := by
  exact add_nonneg (mul_nonneg hk (norm_nonneg _))
    (mul_nonneg (inv_nonneg.mpr hk) (norm_nonneg _))

theorem spectralShellNorm_smul (k : ℝ) (c : ℂ) (u : ℂ × ℂ) :
    spectralShellNorm k (c • u)=‖c‖*spectralShellNorm k u := by
  simp only [spectralShellNorm,Prod.smul_fst,Prod.smul_snd,norm_smul]
  ring

theorem spectralShellNorm_add_le (k : ℝ) (hk : 0≤ k) (u v : ℂ × ℂ) :
    spectralShellNorm k (u+v)≤ spectralShellNorm k u+spectralShellNorm k v := by
  dsimp only [spectralShellNorm,Prod.fst_add,Prod.snd_add]
  calc
    _ ≤ k*(‖u.1‖+‖v.1‖)+k⁻¹*(‖u.2‖+‖v.2‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_add_le _ _) hk)
        (mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hk))
    _ = _ := by ring

theorem spectralShellNorm_value (k : ℝ) (hk : 0<k) (u : ℂ × ℂ) :
    ‖u.1‖ ≤ spectralShellNorm k u/k := by
  apply (le_div_iff₀ hk).mpr
  dsimp only [spectralShellNorm]
  nlinarith [mul_nonneg (inv_nonneg.mpr hk.le) (norm_nonneg u.2)]

theorem spectralShellNorm_slope (k : ℝ) (hk : 0<k) (u : ℂ × ℂ) :
    ‖u.2‖ ≤ k*spectralShellNorm k u := by
  dsimp only [spectralShellNorm]
  have he : k*k⁻¹=1 := mul_inv_cancel₀ hk.ne'
  rw [mul_add,← mul_assoc k k⁻¹,he,one_mul]
  exact le_add_of_nonneg_left (by positivity)

theorem spectralShellNorm_zero (k : ℝ) : spectralShellNorm k 0=0 := by
  simp only [spectralShellNorm,Prod.fst_zero,Prod.snd_zero,norm_zero,mul_zero,add_zero]

theorem spectralShellNorm_eq_zero (k : ℝ) (hk : 0<k) (u : ℂ × ℂ) :
    spectralShellNorm k u=0 ↔ u=0 := by
  constructor
  · intro h
    have hf := spectralShellNorm_value k hk u
    have hg := spectralShellNorm_slope k hk u
    rw [h,zero_div] at hf
    rw [h,mul_zero] at hg
    exact Prod.ext (norm_eq_zero.mp (le_antisymm hf (norm_nonneg _)))
      (norm_eq_zero.mp (le_antisymm hg (norm_nonneg _)))
  · rintro rfl
    exact spectralShellNorm_zero k

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBranchCloseness

namespace OAI

/-! Normalize a logarithmic derivative error by the complex momentum. -/

namespace DefocusingNLS

theorem spectralLogarithmicRatio_bound (p z g chi : ℂ) (eps K : ℝ)
    (hp : p ≠ 0) (_hK : 0 ≤ K)
    (hz : ‖z-(chi*p-g/(4*p^2))‖ ≤ eps*‖p‖)
    (hg : ‖g‖ ≤ K*‖p‖^2) :
    ‖z/p-chi‖ ≤ eps+K/(4*‖p‖) := by
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have he : z/p-chi = (z-(chi*p-g/(4*p^2)))/p-g/(4*p^3) := by field_simp; ring
  rw [he]
  calc
    _ ≤ ‖(z-(chi*p-g/(4*p^2)))/p‖+‖g/(4*p^3)‖ := norm_sub_le _ _
    _ = ‖z-(chi*p-g/(4*p^2))‖/‖p‖+‖g‖/(4*‖p‖^3) := by
      simp only [norm_div,norm_mul,norm_pow,Complex.norm_ofNat]
    _ ≤ eps*‖p‖/‖p‖+(K*‖p‖^2)/(4*‖p‖^3) :=
      add_le_add (div_le_div_of_nonneg_right hz hp0.le)
        (div_le_div_of_nonneg_right hg (by positivity))
    _ = _ := by field_simp

end DefocusingNLS

end OAI

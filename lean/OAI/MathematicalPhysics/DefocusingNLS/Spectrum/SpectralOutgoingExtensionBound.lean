import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! A lower bound on the outgoing value converts the weighted transfer
estimate into a uniform bound for prescribed inner boundary data. -/

namespace DefocusingNLS

theorem spectralOutgoing_extension_bound (k kR B c N Hr HR : ℝ)
    (u uR : ℂ × ℂ) (z : ℂ) (hB : 0 ≤ B) (hc : 0 < c) (hN : 0 < N)
    (horder : Hr ≤ HR)
    (hu : spectralShellNorm k u ≤ B*N*Real.exp Hr)
    (hvalue : c*N*Real.exp HR ≤ kR*‖uR.1‖) :
    spectralShellNorm k ((z/uR.1) • u) ≤ (B/c)*kR*‖z‖ := by
  have hpos : 0 < kR*‖uR.1‖ := (by positivity : 0 < c*N*Real.exp HR).trans_le hvalue
  have hnorm : 0 < ‖uR.1‖ := by
    by_contra hn
    have he : ‖uR.1‖ = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    rw [he,mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hbound : spectralShellNorm k u ≤ (B/c)*kR*‖uR.1‖ := by
    calc
      _ ≤ B*N*Real.exp Hr := hu
      _ ≤ B*N*Real.exp HR := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr horder) (by positivity)
      _ = (B/c)*(c*N*Real.exp HR) := by field_simp [hc.ne',hnorm.ne']
      _ ≤ (B/c)*(kR*‖uR.1‖) := mul_le_mul_of_nonneg_left hvalue (by positivity)
      _ = _ := by ring
  rw [spectralShellNorm_smul, norm_div]
  calc
    _ ≤ (‖z‖/‖uR.1‖)*((B/c)*kR*‖uR.1‖) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by field_simp [hc.ne',hnorm.ne']

end DefocusingNLS

end OAI

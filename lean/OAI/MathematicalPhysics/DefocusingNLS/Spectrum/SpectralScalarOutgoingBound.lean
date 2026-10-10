import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellGreenBounds

namespace OAI

/-! A lower bound for the scalar outgoing value controls its Dirichlet extension.
This is the amplitude estimate used before absorbing the channel coupling. -/

namespace DefocusingNLS

theorem spectralScalarOutgoing_value_ne_zero (k c H : ℝ) (hk : 0<k) (hc : 0<c)
    (U : ℂ × ℂ) (hU : c/k*Real.exp H≤‖U.1‖) : U.1≠0 :=
  norm_pos_iff.mp (lt_of_lt_of_le (mul_pos (div_pos hc hk) (Real.exp_pos _)) hU)

theorem spectralScalarOutgoing_extension_bound (kr kR C c HR Hr : ℝ)
    (hkr : 0≤ kr) (hkR : 0<kR) (hC : 0≤ C) (hc : 0<c) (hH : Hr≤ HR)
    (Ur UR : ℂ × ℂ) (q : ℂ)
    (hUr : spectralShellNorm kr Ur≤ C*Real.exp Hr)
    (hUR : c/kR*Real.exp HR≤‖UR.1‖) :
    spectralShellNorm kr ((q/UR.1) • Ur)≤ C/c*kR*‖q‖ := by
  have hden : 0<c/kR*Real.exp HR := mul_pos (div_pos hc hkR) (Real.exp_pos _)
  have hU0 := spectralShellNorm_nonneg kr hkr Ur
  rw [spectralShellNorm_smul,norm_div]
  calc
    _ ≤ (‖q‖/(c/kR*Real.exp HR))*(C*Real.exp Hr) := by gcongr
    _ ≤ (‖q‖/(c/kR*Real.exp HR))*(C*Real.exp HR) := by gcongr
    _ = _ := by field_simp

end DefocusingNLS

end OAI

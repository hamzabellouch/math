import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePowerBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteLeadingSkew

namespace OAI

/-! Uniform forward and backward propagation for the actual root equation. -/

open Set
namespace DefocusingNLS

theorem spectralRemote_root_propagation
    (c : ℝ → Fin 2 → ℝ) (B : ℝ → SpectralRemoteOperator) (Y : ℝ → SpectralRemoteSpace)
    (s t C : ℝ) (hst : s ≤ t) (hC : 0 ≤ C)
    (hY : ∀ u ∈ Icc s t, HasDerivAt Y ((spectralRemoteLeadingOperator (c u) u+B u) (Y u)) u)
    (hB : ∀ u ∈ Icc s t, ‖B u‖ ≤ C) :
    ‖Y t‖ ≤ 2*Real.exp (4*C*(t-s))*‖Y s‖ ∧
      ‖Y s‖ ≤ 2*Real.exp (4*C*(t-s))*‖Y t‖ := by
  let e := fun u => B u (Y u)
  let omega := fun u => spectralRemoteLeadingFrequency (c u) u
  have hd (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt Y (spectralRemoteSkew (omega u) (Y u)+e u) u := by
    simpa only [add_apply,spectralRemoteLeadingOperator_skew] using hY u hu
  have he (u : ℝ) (hu : u ∈ Icc s t) : ‖e u‖ ≤ C*‖Y u‖ :=
    ((B u).le_opNorm (Y u)).trans (mul_le_mul_of_nonneg_right (hB u hu) (norm_nonneg _))
  exact ⟨spectralRemote_norm_growth Y e omega s t C hst hC hd he,
    spectralRemote_norm_growth_reverse Y e omega s t C hst hC hd he⟩

end DefocusingNLS

end OAI

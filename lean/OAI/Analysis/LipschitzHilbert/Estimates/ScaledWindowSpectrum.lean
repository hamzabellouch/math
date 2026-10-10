import OAI.Analysis.LipschitzHilbert.Fourier.ScaledWindowFourier

namespace OAI

/-! The fixed frequency plateaus give the original narrow spectra for
both actual packet kernels, uniformly in their Fourier-series parameter. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem scaledWindow_inverse_profile_apply (chi : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ) :
    scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center)
      hl.ne' hW.ne' (xi,eta)=chi (symbolX l xi eta theta,symbolY W eta center) := by
  rw [scaledFrequencyWindow_apply _ l W theta center hl hW, planarInverseSchwartz_fourier]

theorem horizontalFrequencyKernel_zero_of_window_zero (A : SchwartzMap (ℝ×ℝ) ℂ)
    (nu : SymbolSpace) (q : ℕ) (l theta : ℝ) (omega : ℝ×ℝ) (hz : A omega=0) :
    planarFourier (horizontalFrequencyKernel A nu q l theta) omega=0 := by
  rw [horizontalFrequencyKernel, planarInverseSchwartz_fourier]
  simp only [smul_apply, smul_eq_mul, modulatedFrequencyWindow_apply, hz, mul_zero]

theorem verticalFrequencyKernel_zero_of_window_zero (B : SchwartzMap (ℝ×ℝ) ℂ)
    (nu : SymbolSpace) (q : ℕ) (W center : ℝ) (omega : ℝ×ℝ) (hz : B omega=0) :
    planarFourier (verticalFrequencyKernel B nu q W center) omega=0 := by
  rw [verticalFrequencyKernel, planarInverseSchwartz_fourier]
  simp only [smul_apply, smul_eq_mul, modulatedFrequencyWindow_apply, hz, mul_zero]

theorem scaledWindow_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ)
    (h : scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center)
      hl.ne' hW.ne' (xi,eta)≠0) :
    |xi+theta*eta|≤A/l ∧ |eta-center|≤B/W := by
  rw [scaledWindow_inverse_profile_apply _ l W theta center hl hW] at h
  have hh := hchi _ h
  constructor
  · apply (le_div_iff₀ hl).2
    simpa only [symbolX, abs_mul, abs_of_pos hl, mul_comm] using hh.1
  · apply (le_div_iff₀ hW).2
    simpa only [symbolY, abs_mul, abs_of_pos hW, mul_comm] using hh.2

theorem horizontal_scaled_kernel_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ)
    (h : planarFourier (horizontalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q l theta) (xi,eta)≠0) :
    |xi+theta*eta|≤A/l ∧ |eta-center|≤B/W := by
  apply scaledWindow_support chi A B hchi l W theta center hl hW xi eta
  intro hz
  exact h (horizontalFrequencyKernel_zero_of_window_zero _ nu q l theta (xi,eta) hz)

theorem vertical_scaled_kernel_support (chi : SchwartzMap (ℝ×ℝ) ℂ) (A B : ℝ)
    (hchi : ∀ z, chi z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) (xi eta : ℝ)
    (h : planarFourier (verticalFrequencyKernel
      (scaledFrequencyWindow (planarInverseSchwartz chi) l W theta (2*Real.pi*center) hl.ne' hW.ne')
        nu q W center) (xi,eta)≠0) :
    |xi+theta*eta|≤A/l ∧ |eta-center|≤B/W := by
  apply scaledWindow_support chi A B hchi l W theta center hl hW xi eta
  intro hz
  exact h (verticalFrequencyKernel_zero_of_window_zero _ nu q W center (xi,eta) hz)

end LipschitzHilbert.PacketRepresentation

end

end OAI

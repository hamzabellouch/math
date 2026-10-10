import OAI.Analysis.LipschitzHilbert.Packets.PlanarFrequencyPackets
import OAI.Analysis.LipschitzHilbert.Packets.ConvolutionPacketProfile

namespace OAI

/-! Fourier characters translate the actual convolution kernels.
Their translation vectors follow the packet's long and short coordinates. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverse_modulatedFrequencyWindow (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a b c : ℝ) (x : ℝ×ℝ) :
    planarInverseSchwartz (modulatedFrequencyWindow F a b c) x=
      (Real.fourierChar c:ℂ)*planarInverseSchwartz F (x+(a,b)) := by
  rw [planarInverseSchwartz_apply, planarInverseSchwartz_apply, planarInverse,
    planarInverse, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [modulatedFrequencyWindow_apply]
  simp only [Circle.smul_def, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  simp only [Real.fourierChar_apply, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem planarInverseSchwartz_smul (c : ℂ) (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz (c • F) x=c*planarInverseSchwartz F x := by
  rw [planarInverseSchwartz_apply, planarInverseSchwartz_apply]
  exact planarInverse_const_mul c F x

theorem horizontalFrequencyKernel_apply (A : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l theta : ℝ) (x : ℝ×ℝ) :
    horizontalFrequencyKernel A nu q l theta x=
      (symbolWeight q nu:ℂ)*planarInverseSchwartz A (x+(nu 0*l,nu 0*l*theta)) := by
  rw [horizontalFrequencyKernel, planarInverseSchwartz_smul,
    planarInverse_modulatedFrequencyWindow]
  simp only [Real.fourierChar_apply, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_mul]

theorem verticalFrequencyKernel_apply (B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (W center : ℝ) (x : ℝ×ℝ) :
    verticalFrequencyKernel B nu q W center x=
      (symbolWeight q nu:ℂ)*(Real.fourierChar (-(nu 1*W*center)):ℂ)*
        planarInverseSchwartz B (x+(0,nu 1*W)) := by
  rw [verticalFrequencyKernel, planarInverseSchwartz_smul,
    planarInverse_modulatedFrequencyWindow]
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI

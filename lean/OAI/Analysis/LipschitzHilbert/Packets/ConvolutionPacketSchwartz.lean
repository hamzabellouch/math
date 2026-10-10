import OAI.Analysis.LipschitzHilbert.Packets.ConvolutionPacketSpectrum

namespace OAI

/-! The actual analyzing and synthesizing convolution waves as Schwartz
functions, including the reflected-conjugate analyzing kernel. -/
noncomputable section
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def synthesisPacket (area : ℝ) (K : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  (area:ℂ) • K.compSubConstCLM ℂ z

def analyzingPacket (area : ℝ) (K : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  (area:ℂ) • ((SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ (E := ℝ×ℝ)) K).postcompCLM
      (Complex.conjCLE.toContinuousLinearMap)).compSubConstCLM ℂ z

theorem synthesisPacket_apply (area : ℝ) (K : SchwartzMap (ℝ×ℝ) ℂ) (z x : ℝ×ℝ) :
    synthesisPacket area K z x=synthesisWave area K z x := rfl

theorem analyzingPacket_apply (area : ℝ) (K : SchwartzMap (ℝ×ℝ) ℂ) (z x : ℝ×ℝ) :
    analyzingPacket area K z x=analyzingWave area K z x := by
  change (area:ℂ)*conj (K (-(x-z)))=(area:ℂ)*conj (K (z-x))
  rw [neg_sub]

theorem synthesisPacket_spectrum {S : Set (ℝ×ℝ)} (area : ℝ)
    (K : SchwartzMap (ℝ×ℝ) ℂ)
    (hK : ∀ omega, planarAngularFourier K omega≠0 → omega∈S)
    (z omega : ℝ×ℝ) (h : planarAngularFourier (synthesisPacket area K z) omega≠0) : omega∈S := by
  apply synthesisWave_spectrum area K hK z omega
  simpa only [funext (synthesisPacket_apply area K z)] using h

theorem analyzingPacket_spectrum {S : Set (ℝ×ℝ)} (area : ℝ)
    (K : SchwartzMap (ℝ×ℝ) ℂ)
    (hK : ∀ omega, planarAngularFourier K omega≠0 → omega∈S)
    (z omega : ℝ×ℝ) (h : planarAngularFourier (analyzingPacket area K z) omega≠0) : omega∈S := by
  apply analyzingWave_spectrum area K hK z omega
  simpa only [funext (analyzingPacket_apply area K z)] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI

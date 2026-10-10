import OAI.Analysis.LipschitzHilbert.Packets.ConvolutionPacketSchwartz
import OAI.Analysis.LipschitzHilbert.Trees.SourceVerticalDemodulation

namespace OAI

/-! Normalized Schwartz profiles for the actual convolution packets,
with arbitrary prescribed vertical carrier. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def convolutionProfile (K : SchwartzMap (ℝ×ℝ) ℂ) (l W theta nu : ℝ)
    (hl : l≠0) (hW : W≠0) : SchwartzMap (ℝ×ℝ) ℂ :=
  (l*W:ℂ) • scalarVerticalDemodulation (nu*W)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (packetCoordinates l W theta hl hW).symm K)

theorem convolutionProfile_apply (K : SchwartzMap (ℝ×ℝ) ℂ) (l W theta nu : ℝ)
    (hl : l≠0) (hW : W≠0) (q : ℝ×ℝ) :
    convolutionProfile K l W theta nu hl hW q =
      (l*W:ℂ)*Complex.exp ((-(nu*W)*q.2:ℝ)*Complex.I)*
        K ((packetCoordinates l W theta hl hW).symm q) := by
  rw [convolutionProfile, smul_apply, scalarVerticalDemodulation_apply]
  simp only [verticalCarrier, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, smul_eq_mul]
  ring

theorem physical_convolution_packet (K : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta nu : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (convolutionProfile K l W theta nu hl hW)
      z.1 z.2 l W theta nu hl hW x=synthesisWave (l*W) K z x := by
  rw [physicalPlanarPacket_apply, convolutionProfile_apply]
  have harg : (packetCoordinates l W theta hl hW).symm
      ((x.1-z.1)/l,((x.2-z.2)-theta*(x.1-z.1))/W)=x-z :=
    (packetCoordinates l W theta hl hW).symm_apply_apply (x-z)
  rw [harg]
  have hp : ((nu*((x.2-z.2)-theta*(x.1-z.1)):ℝ):ℂ)*Complex.I+
      ((-(nu*W)*(((x.2-z.2)-theta*(x.1-z.1))/W):ℝ):ℂ)*Complex.I=0 := by
    push_cast
    field_simp [show (W:ℂ)≠0 by exact_mod_cast hW]
    ring
  calc
    _ = (Complex.exp (((nu*((x.2-z.2)-theta*(x.1-z.1)):ℝ):ℂ)*Complex.I)*
        Complex.exp (((-(nu*W)*(((x.2-z.2)-theta*(x.1-z.1))/W):ℝ):ℂ)*Complex.I))*
          ((l*W:ℂ)*K (x-z)) := by ring
    _ = _ := by
      rw [← Complex.exp_add, hp, Complex.exp_zero, one_mul]
      simp only [synthesisWave, Complex.ofReal_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI

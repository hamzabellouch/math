import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSchwartzInversion
import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeAverage
import Mathlib.Analysis.Fourier.Convolution

namespace OAI

/-! A factored frequency multiplier is exactly the normalized average
of its actual analyzing and synthesizing convolution packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert

def lowerHilbertPlanarSchwartz (F : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm F

theorem hilbertPlanar_lower (F : SchwartzMap (WithLp 2 (ℝ×ℝ)) ℂ) :
    hilbertPlanarSchwartz (lowerHilbertPlanarSchwartz F)=F := by
  ext x
  rfl

def planarSchwartzConvolution (K f : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  lowerHilbertPlanarSchwartz (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (hilbertPlanarSchwartz f) (hilbertPlanarSchwartz K))

theorem planarSchwartzConvolution_apply (K f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarSchwartzConvolution K f x=PacketRepresentation.kernelConvolution K f x := by
  change SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (hilbertPlanarSchwartz f) (hilbertPlanarSchwartz K) (WithLp.toLp 2 x)=_
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution, integral_hilbertPlanar_bridge]
  rfl

theorem planarFourier_convolution (K f : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (planarSchwartzConvolution K f) omega=
      planarFourier K omega*planarFourier f omega := by
  rw [← fourier_hilbertPlanar_bridge, planarSchwartzConvolution, hilbertPlanar_lower,
    SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    fourier_hilbertPlanar_bridge, fourier_hilbertPlanar_bridge]
  exact mul_comm _ _

namespace PacketRepresentation

theorem factored_multiplier_convolution (KA KB f : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverse (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega) x=
      kernelConvolution KA (kernelConvolution KB f) x := by
  have heq : (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega)=
      planarFourier (planarSchwartzConvolution KA (planarSchwartzConvolution KB f)) := by
    funext omega
    rw [planarFourier_convolution, planarFourier_convolution, mul_assoc]
  rw [heq, planarFourier_inversion, planarSchwartzConvolution_apply,
    funext (planarSchwartzConvolution_apply KB f)]

theorem factored_multiplier_packet_average (KA KB f : SchwartzMap (ℝ×ℝ) ℂ)
    (b g : ℝ×ℝ → ℂ) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg)
    (l W theta : ℝ) (hl : 0<l) (hW : 0<W) :
    (∫ x, b x*planarInverse
      (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega) x*
      conj (g x) ∂planeMeasure) =
      ∫ z, ∑' n : ℤ×ℤ, ((l*W:ℝ):ℂ)⁻¹ *
        packetProduct KA KB f b g (l*W) (latticeHom l W theta n+z)
        ∂latticeAverage l W theta := by
  simp_rw [factored_multiplier_convolution]
  exact averaged_packet_identity KA KB f b g KA.integrable KB.integrable f.integrable
    hb hg Mb Mg hbb hgb l W theta hl hW

end PacketRepresentation
end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.L1FourierConvolution

namespace OAI

/-! The two Schwartz frequency factors retain their exact convolution
representation on every L1 amplitude slice. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelConvolution_schwartz_assoc_l1 (KA KB : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (x : ℝ×ℝ) :
    kernelConvolution (planarSchwartzConvolution KA KB) f x=
      kernelConvolution KA (kernelConvolution KB f) x := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hKA : Integrable KA planeMeasure := KA.integrable
  have hKB : Integrable KB planeMeasure := KB.integrable
  have hfg := hf.ae_convolution_exists L hKB
  have hgk := hKB.ae_convolution_exists L hKA
  have hi : Integrable (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
      (f p.2*KB (p.1-p.2))*KA (x-p.1)) (planeMeasure.prod planeMeasure) := by
    apply (hf.convolution_integrand L hKB).mul_bdd (c:=SchwartzMap.seminorm ℝ 0 0 KA)
    · exact (KA.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => SchwartzMap.norm_le_seminorm ℝ KA _)
  have h := convolution_assoc' (x₀:=x) L L L L (fun a b c => mul_assoc a b c) hfg hgk
    (by
      apply hi.congr
      filter_upwards [] with p
      change (f p.2*KB (p.1-p.2))*KA (x-p.1)=f p.2*(KB (p.1-p.2)*KA (x-p.1))
      ring)
  have heq : (planarSchwartzConvolution KA KB : ℝ×ℝ → ℂ)=kernelConvolution KA KB :=
    funext (planarSchwartzConvolution_apply KA KB)
  rw [heq]
  exact h.symm

theorem factored_multiplier_convolution_l1 (KA KB : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (x : ℝ×ℝ) :
    planarInverse (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega) x=
      kernelConvolution KA (kernelConvolution KB f) x := by
  have heq : (fun omega => planarFourier KA omega*planarFourier KB omega*planarFourier f omega)=
      (fun omega => planarFourier (planarSchwartzConvolution KA KB) omega*planarFourier f omega) := by
    funext omega
    rw [planarFourier_convolution]
  rw [heq,planarInverse_mul_fourier_l1 _ f hf,kernelConvolution_schwartz_assoc_l1 KA KB f hf]

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Packets.FactoredMultiplierPackets
import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedSymbolOperator

namespace OAI

/-! The two separated frequency factors are Fourier transforms of actual
Schwartz convolution kernels. Thus the lattice average uses actual packets. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def planarInverseSchwartz (F : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  lowerHilbertPlanarSchwartz (𝓕⁻ (hilbertPlanarSchwartz F))

theorem planarInverseSchwartz_fourier (F : SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (planarInverseSchwartz F) omega=F omega := by
  rw [← fourier_hilbertPlanar_bridge, planarInverseSchwartz, hilbertPlanar_lower,
    FourierTransform.fourier_fourierInv_eq, hilbertPlanarSchwartz_apply]

theorem planarInverseSchwartz_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ×ℝ) :
    planarInverseSchwartz F x=planarInverse F x := by
  rw [← planarFourier_inversion (planarInverseSchwartz F) x]
  congr 1
  funext omega
  exact planarInverseSchwartz_fourier F omega

theorem affineFrequencyCharacter_temperate (a b c : ℝ) :
    Function.HasTemperateGrowth (fun omega : ℝ×ℝ =>
      (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)) := by
  have hx : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.1) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  have hy : Function.HasTemperateGrowth (fun omega : ℝ×ℝ => omega.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

def modulatedFrequencyWindow (F : SchwartzMap (ℝ×ℝ) ℂ) (a b c : ℝ) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun omega : ℝ×ℝ =>
    (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)) F

theorem modulatedFrequencyWindow_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (a b c : ℝ) (omega : ℝ×ℝ) :
    modulatedFrequencyWindow F a b c omega=
      (Real.fourierChar (a*omega.1+b*omega.2+c):ℂ)*F omega :=
  SchwartzMap.smulLeftCLM_apply_apply (affineFrequencyCharacter_temperate a b c) F omega

def horizontalFrequencyKernel (A : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l theta : ℝ) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarInverseSchwartz ((symbolWeight q nu:ℂ) •
    modulatedFrequencyWindow A (nu 0*l) (nu 0*l*theta) 0)

def verticalFrequencyKernel (B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (W center : ℝ) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarInverseSchwartz ((symbolWeight q nu:ℂ) •
    modulatedFrequencyWindow B 0 (nu 1*W) (-(nu 1*W*center)))

theorem frequencyKernel_product (A B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l W theta center : ℝ) (omega : ℝ×ℝ) :
    planarFourier (horizontalFrequencyKernel A nu q l theta) omega*
      planarFourier (verticalFrequencyKernel B nu q W center) omega=
        (symbolWeight q nu:ℂ)^2*
          modulatedFrequency (fun omega => A omega*B omega) nu l W theta center omega := by
  rw [horizontalFrequencyKernel, verticalFrequencyKernel,
    planarInverseSchwartz_fourier, planarInverseSchwartz_fourier]
  simp only [smul_apply, smul_eq_mul, modulatedFrequencyWindow_apply,
    modulatedFrequency, frequencyCharacter]
  have hx : nu 0*l*omega.1+nu 0*l*theta*omega.2+0=
      nu 0*symbolX l omega.1 omega.2 theta := by unfold symbolX; ring
  have hy : 0*omega.1+nu 1*W*omega.2+ -(nu 1*W*center)=
      nu 1*symbolY W omega.2 center := by unfold symbolY; ring
  rw [hx,hy]
  ring

theorem frequencyKernel_packet_average (A B f : SchwartzMap (ℝ×ℝ) ℂ)
    (b g : ℝ×ℝ → ℂ) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg)
    (nu : SymbolSpace) (q : ℕ) (l W theta center : ℝ) (hl : 0<l) (hW : 0<W) :
    (∫ x, b x*planarInverse (fun omega => (symbolWeight q nu:ℂ)^2*
        modulatedFrequency (fun omega => A omega*B omega) nu l W theta center omega*
          planarFourier f omega) x*conj (g x) ∂planeMeasure)=
      ∫ z, ∑' n : ℤ×ℤ, ((l*W:ℝ):ℂ)⁻¹ *
        packetProduct (horizontalFrequencyKernel A nu q l theta)
          (verticalFrequencyKernel B nu q W center) f b g (l*W) (latticeHom l W theta n+z)
          ∂latticeAverage l W theta := by
  have h := factored_multiplier_packet_average (horizontalFrequencyKernel A nu q l theta)
    (verticalFrequencyKernel B nu q W center) f b g hb hg Mb Mg hbb hgb l W theta hl hW
  simpa only [frequencyKernel_product] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI

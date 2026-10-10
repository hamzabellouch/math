import OAI.Analysis.LipschitzHilbert.Fourier.ConvolutionPowerTail

namespace OAI

/-! The distribution estimate for interpolation between uniform second
and fourth convolution moments. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem normPower_lintegral_le_of_integral (f g : ℝ → ℂ) (n : ℕ)
    (hf : Integrable (fun x => ‖f x‖^n)) (hg : Integrable (fun x => ‖g x‖^n))
    (A : ℝ) (hA : 0≤A) (h : (∫ x, ‖g x‖^n)≤A*(∫ x, ‖f x‖^n)) :
    (∫⁻ x, ENNReal.ofReal (‖g x‖^n))≤ENNReal.ofReal A*(∫⁻ x, ENNReal.ofReal (‖f x‖^n)) := by
  rw [←ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun x => by positivity),
    ←ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun x => by positivity),
    ←ENNReal.ofReal_mul hA]
  exact ENNReal.ofReal_le_ofReal h

theorem convolution_layer_tail (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4))
    (t : ℝ) (ht : 0<t) :
    ENNReal.ofReal (t^2)*volume {x | t≤‖lineConvolution K f x‖}≤
      ENNReal.ofReal (4*A^2)*highLayerEnergy f t+
      ENNReal.ofReal (16*C^4)*(ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t) := by
  let fh := highAmplitude f t
  let fl := lowAmplitude f t
  have hhm : Measurable fh := highAmplitude_measurable f hf t
  have hlm : Measurable fl := lowAmplitude_measurable f hf t
  have hh2 : MemLp fh 2 volume := hf2.indicator (measurableSet_le measurable_const hf.norm)
  have hl4 : MemLp fl 4 volume := hf4.indicator (measurableSet_lt hf.norm measurable_const)
  have hhb (x : ℝ) : ‖fh x‖≤M := (amplitude_bound f t x).1.trans (hM x)
  have hlb (x : ℝ) : ‖fl x‖≤M := (amplitude_bound f t x).2.trans (hM x)
  have hhOut := (lineConvolution_energy_bound K hK hKm fh hhm hh2).1
  have hlOut := (lineConvolution_L4_bound K fl hK hKm hlm hl4).1
  have eh := normPower_lintegral_le_of_integral fh (lineConvolution K fh) 2
    (hh2.integrable_norm_pow (by decide)) (hhOut.integrable_norm_pow (by decide))
    (A^2) (sq_nonneg A) (boundedConvolution_L2_of_schwartz K hK hKm A hA h2 fh hhm hh2 M hhb)
  have el := normPower_lintegral_le_of_integral fl (lineConvolution K fl) 4
    (hl4.integrable_norm_pow (by decide)) (hlOut.integrable_norm_pow (by decide))
    (C^4) (by positivity) (boundedConvolution_L4_of_schwartz K hK hKm C hC h4 fl hlm hl4 M hlb)
  rw [highAmplitude_power] at eh
  rw [lowAmplitude_power] at el
  have hhTail := (normPower_tail (lineConvolution K fh) (lineConvolution_measurable K hKm fh hhm)
    2 (t/2) (by positivity)).trans (mul_le_mul_right eh _)
  have hlTail := (normPower_tail (lineConvolution K fl) (lineConvolution_measurable K hKm fl hlm)
    4 (t/2) (by positivity)).trans (mul_le_mul_right el _)
  have hset : {x | t≤‖lineConvolution K f x‖}⊆
      {x | t/2≤‖lineConvolution K fh x‖}∪{x | t/2≤‖lineConvolution K fl x‖} := by
    intro x hx
    change t≤‖lineConvolution K f x‖ at hx
    rw [convolution_amplitude_sum K f hK hf M hM t x] at hx
    by_contra hn
    simp only [mem_union,mem_ofPred_eq,not_or,not_le] at hn
    have htri := norm_add_le (lineConvolution K fh x) (lineConvolution K fl x)
    linarith
  have htail := (measure_mono hset).trans (measure_union_le (μ:=volume) _ _)
  have hc2 : ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2))=
      ENNReal.ofReal (4*A^2) := by
    rw [←ENNReal.ofReal_pow (by positivity),←ENNReal.ofReal_mul (by positivity),
      ←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp; ring
  have hc4 : ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4))=
      ENNReal.ofReal (16*C^4)*ENNReal.ofReal (t^(-2:ℝ)) := by
    rw [←ENNReal.ofReal_pow (by positivity),←ENNReal.ofReal_mul (by positivity),
      ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_neg ht.le,Real.rpow_two]
    field_simp; ring
  calc
    _ ≤ ENNReal.ofReal (t^2)*(volume {x | t/2≤‖lineConvolution K fh x‖}+
        volume {x | t/2≤‖lineConvolution K fl x‖}) := mul_le_mul_right htail _
    _ ≤ ENNReal.ofReal (t^2)*
        ((ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2))*highLayerEnergy f t+
        (ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4))*lowLayerEnergy f t) := by
      exact mul_le_mul_right (add_le_add (by simpa only [mul_assoc] using hhTail)
        (by simpa only [mul_assoc] using hlTail)) _
    _ = (ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^2*ENNReal.ofReal (A^2)))*highLayerEnergy f t+
        (ENNReal.ofReal (t^2)*(ENNReal.ofReal ((t/2)⁻¹)^4*ENNReal.ofReal (C^4)))*lowLayerEnergy f t := by ring
    _ = _ := by rw [hc2,hc4,mul_assoc]

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.LayerEnergyMoments
import OAI.Analysis.LipschitzHilbert.Fourier.BoundedConvolutionL2
import OAI.Analysis.LipschitzHilbert.Fourier.BoundedConvolutionL4

namespace OAI

/-! Markov estimates and the actual large/small amplitude splitting used
for interpolation of line convolutions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem normPower_tail (g : ℝ → ℂ) (hgm : Measurable g) (n : ℕ)
    (t : ℝ) (ht : 0<t) :
    volume {x | t≤‖g x‖}≤ENNReal.ofReal (t⁻¹)^n*(∫⁻ x, ENNReal.ofReal (‖g x‖^n)) := by
  have hinc : {x | t≤‖g x‖}⊆{x | ENNReal.ofReal (t^n)≤ENNReal.ofReal (‖g x‖^n)} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le hx n)
  have hpos : ENNReal.ofReal (t^n)≠0 := by positivity
  have hh := meas_ge_le_lintegral_div (μ:=volume)
    ((hgm.norm.pow_const n).ennreal_ofReal.aemeasurable) hpos ENNReal.ofReal_ne_top
  calc
    _ ≤ volume {x | ENNReal.ofReal (t^n)≤ENNReal.ofReal (‖g x‖^n)} := measure_mono hinc
    _ ≤ (∫⁻ x, ENNReal.ofReal (‖g x‖^n))/ENNReal.ofReal (t^n) := hh
    _ = _ := by
      rw [ENNReal.ofReal_pow ht.le,div_eq_mul_inv,ENNReal.inv_pow,
        ←ENNReal.ofReal_inv_of_pos ht,mul_comm]

def highAmplitude (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := {x | t≤‖f x‖}.indicator f

def lowAmplitude (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := {x | ‖f x‖<t}.indicator f

theorem highAmplitude_measurable (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Measurable (highAmplitude f t) := hf.indicator (measurableSet_le measurable_const hf.norm)

theorem lowAmplitude_measurable (f : ℝ → ℂ) (hf : Measurable f) (t : ℝ) :
    Measurable (lowAmplitude f t) := hf.indicator (measurableSet_lt hf.norm measurable_const)

theorem amplitude_sum (f : ℝ → ℂ) (t x : ℝ) : highAmplitude f t x+lowAmplitude f t x=f x := by
  classical
  unfold highAmplitude lowAmplitude
  by_cases hx : t≤‖f x‖ <;> simp [hx,not_lt.mpr,lt_of_not_ge]

theorem amplitude_bound (f : ℝ → ℂ) (t x : ℝ) :
    ‖highAmplitude f t x‖≤‖f x‖ ∧ ‖lowAmplitude f t x‖≤‖f x‖ := by
  classical
  unfold highAmplitude lowAmplitude
  constructor <;> exact norm_indicator_le_norm_self f x

theorem convolution_amplitude_sum (K f : ℝ → ℂ) (hK : Integrable K)
    (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖≤B) (t x : ℝ) :
    lineConvolution K f x=lineConvolution K (highAmplitude f t) x+
      lineConvolution K (lowAmplitude f t) x := by
  have hh := lineConvolution_integrand_of_bounded K (highAmplitude f t) hK
    (highAmplitude_measurable f hf t) B (fun x => (amplitude_bound f t x).1.trans (hB x)) x
  have hl := lineConvolution_integrand_of_bounded K (lowAmplitude f t) hK
    (lowAmplitude_measurable f hf t) B (fun x => (amplitude_bound f t x).2.trans (hB x)) x
  rw [lineConvolution,lineConvolution,lineConvolution,←integral_add hh hl]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [←mul_add,amplitude_sum]

theorem highAmplitude_power (f : ℝ → ℂ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖highAmplitude f t x‖^2))=highLayerEnergy f t := by
  classical
  apply lintegral_congr
  intro x
  unfold highAmplitude
  by_cases hx : t≤‖f x‖ <;> simp [hx]

theorem lowAmplitude_power (f : ℝ → ℂ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖lowAmplitude f t x‖^4))=lowLayerEnergy f t := by
  classical
  apply lintegral_congr
  intro x
  unfold lowAmplitude
  by_cases hx : ‖f x‖<t <;> simp [hx]

end LipschitzHilbert.PacketRepresentation

end

end OAI

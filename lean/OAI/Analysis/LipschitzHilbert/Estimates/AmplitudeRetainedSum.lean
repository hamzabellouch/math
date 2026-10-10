import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeClassCount
import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeNormalizedEnergy

namespace OAI

/-! The retained level sum has the square-root logarithmic loss needed
by the improved diagonal estimate. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem retained_amplitude_sum (I : Finset ℤ) (mass : ℤ → ℝ) (L E : ℝ)
    (hL : 0≤L) (hm : ∀ i∈I, 0<mass i)
    (hlog : ∀ i∈I, |Real.log (mass i)|≤L)
    (henergy : (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mass i))^2)≤E) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt (2*(L/Real.log 2)+5)*Real.sqrt E := by
  have h := dyadic_amplitude_class_sum I mass hm
  apply h.trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (dyadicMeasureClass_image_card I mass L hL hlog))
    positivity
  · exact Real.sqrt_le_sqrt henergy
  · exact Real.sqrt_nonneg _
  · positivity

theorem amplitudeLevel_retained_sum {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (mu : Measure X) (f : X → E) (hf : MemLp f 2 mu)
    (hm : Measurable (fun x => ‖f x‖)) (I : Finset ℤ) (M0 C0 L : ℝ)
    (hM0 : 0<M0) (hL : 0≤L) (henergy : (∫ x, ‖f x‖^2 ∂mu)≤C0*M0)
    (hpos : ∀ i∈I, 0<mu.real (amplitudeLevel f i))
    (hlog : ∀ i∈I, |Real.log (mu.real (amplitudeLevel f i)/M0)|≤L) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      4*Real.sqrt 2*Real.sqrt (2*(L/Real.log 2)+5)*Real.sqrt (4*C0) :=
  retained_amplitude_sum I (fun i => mu.real (amplitudeLevel f i)/M0) L (4*C0)
    hL (fun i hi => div_pos (hpos i hi) hM0) hlog
    (amplitude_normalized_energy_budget mu f hf hm M0 C0 hM0 henergy I)

end LipschitzHilbert

end

end OAI

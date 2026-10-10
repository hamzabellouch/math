import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeLevelL1

namespace OAI

/-! Normalize the actual amplitude-level energy by the reference set
measure, as used in the bin reduction. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitude_normalized_energy_budget (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (M0 C0 : ℝ) (hM0 : 0<M0) (henergy : (∫ x, ‖f x‖^2 ∂mu)≤C0*M0) (I : Finset ℤ) :
    (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))^2)≤4*C0 := by
  have heq : (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))^2)=
      (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)))^2)/M0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow,mul_pow,Real.sq_sqrt (div_nonneg measureReal_nonneg hM0.le),Real.sq_sqrt measureReal_nonneg]
    ring
  rw [heq]
  apply (div_le_iff₀ hM0).mpr
  have h := amplitude_energy_budget mu hf hm I
  nlinarith

theorem amplitudeLevel_small_tail (mu : Measure X) (f : X → E)
    (I : Finset ℤ) (M0 Q eps : ℝ) (hM0 : 0<M0) (hQ : 0≤Q) (heps : 0≤eps)
    (hbound : ∀ x, ‖f x‖≤Q) (hpos : ∀ i∈I, 0<mu.real (amplitudeLevel f i))
    (hsmall : ∀ i∈I, mu.real (amplitudeLevel f i)≤eps*M0) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤8*Q*Real.sqrt eps :=
  amplitude_small_mass_tail I (fun i => mu.real (amplitudeLevel f i)) M0 Q eps hM0 hQ heps
    (fun i hi => amplitudeLevel_amplitude_bound mu f Q hbound i (hpos i hi)) hsmall

theorem amplitudeLevel_large_tail (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hL1 : Integrable (fun x => ‖f x‖) mu)
    (I : Finset ℤ) (M0 Q eps : ℝ) (hM0 : 0<M0) (hQ : 0≤Q) (heps : 0<eps)
    (hbound : (∫ x, ‖f x‖ ∂mu)≤Q*M0)
    (hlarge : ∀ i∈I, M0≤eps*mu.real (amplitudeLevel f i)) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      2*(2/(1-(Real.sqrt 2)⁻¹))*Q*Real.sqrt eps := by
  apply amplitude_large_mass_tail I (fun i => mu.real (amplitudeLevel f i)) M0 Q eps
    hM0 hQ heps (fun _ _ => measureReal_nonneg) hlarge
  intro i _
  have h := amplitudeLevel_l1_bound mu f hf hm hL1 i
  nlinarith

end LipschitzHilbert

end

end OAI

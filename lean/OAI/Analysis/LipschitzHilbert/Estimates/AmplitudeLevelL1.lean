import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeEnergy
import OAI.Analysis.LipschitzHilbert.Trees.AmplitudeMassTails

namespace OAI

/-! The numerical amplitude tail hypotheses follow from the actual
pointwise and L1 bounds of the bin-projected vector. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem amplitudeLevel_amplitude_bound (mu : Measure X) (f : X → E)
    (Q : ℝ) (hQ : ∀ x, ‖f x‖≤Q) (i : ℤ)
    (hpos : 0<mu.real (amplitudeLevel f i)) : (2:ℝ)^i≤2*Q := by
  have hn : (amplitudeLevel f i).Nonempty := by
    by_contra h
    have he : amplitudeLevel f i=∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hpos
  obtain ⟨x,hx⟩ := hn
  have h := hx.1.trans_le (hQ x)
  have he : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
    rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
    norm_num
    ring
  rw [he]
  linarith

theorem amplitudeLevel_l1_bound (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hL1 : Integrable (fun x => ‖f x‖) mu) (i : ℤ) :
    (2:ℝ)^i*mu.real (amplitudeLevel f i)≤2*∫ x, ‖f x‖ ∂mu := by
  have hset := amplitudeLevel_measurable hm i
  have hi : IntegrableOn (fun _ : X => (2:ℝ)^(i-1)) (amplitudeLevel f i) mu :=
    integrableOn_const (amplitudeLevel_finite mu hf i)
  have hlow : (∫ _ in amplitudeLevel f i, (2:ℝ)^(i-1) ∂mu)≤
      ∫ x in amplitudeLevel f i, ‖f x‖ ∂mu := by
    apply setIntegral_mono_on hi hL1.integrableOn hset
    intro x hx
    exact hx.1.le
  have hfull := setIntegral_le_integral hL1 (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (s:=amplitudeLevel f i)
  rw [setIntegral_const,smul_eq_mul] at hlow
  have he : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
    rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
    norm_num
    ring
  rw [he]
  nlinarith

end LipschitzHilbert

end

end OAI

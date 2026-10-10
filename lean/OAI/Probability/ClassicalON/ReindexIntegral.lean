import OAI.Probability.ClassicalON.PinnedBlocks

namespace OAI

universe uA uV uW

noncomputable section
open MeasureTheory
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {A : Type uA} [Fintype V] [Fintype W] [MeasurableSpace A]

theorem integral_pi_reindex (e : V ≃ W) (μ : W → Measure A) [∀ w,SigmaFinite (μ w)]
    (f : (V → A) → ℝ) :
    (∫ s : W → A,f (fun v => s (e v)) ∂Measure.pi μ)=
      ∫ s : V → A,f s ∂Measure.pi (fun v => μ (e v)) := by
  have h := (measurePreserving_piCongrLeft (fun v => μ (e v)) e.symm).integral_comp' f
  have he (s : W → A) : MeasurableEquiv.piCongrLeft (fun _ : V => A) e.symm s=(fun v => s (e v)) := by
    funext v
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  simpa only [he,Equiv.apply_symm_apply] using h

theorem weightedMean_pi_reindex (e : V ≃ W) (μ : W → Measure A) [∀ w,SigmaFinite (μ w)]
    (w f : (V → A) → ℝ) :
    weightedMean (Measure.pi μ) (fun s => w (fun v => s (e v))) (fun s => f (fun v => s (e v)))=
      weightedMean (Measure.pi (fun v => μ (e v))) w f := by
  unfold weightedMean
  rw [integral_pi_reindex e μ (fun s => w s*f s),integral_pi_reindex e μ w]

end ClassicalON

end

end OAI

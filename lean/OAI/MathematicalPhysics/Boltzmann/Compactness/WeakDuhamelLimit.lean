import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative

namespace OAI

/-! # Passing the characteristic initial-value identity through the weak limits -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem weak_duhamel_limit {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f r : ℕ → ℝ × Phase → ℝ} {g R : ℝ × Phase → ℝ}
    {a : ℕ → Phase → ℝ} {a₀ : Phase → ℝ}
    (hf : Published.WeakL1Converges (μ.prod volume) f g)
    (hr : Published.WeakL1Converges (μ.prod volume) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod volume))
    (ha : Published.WeakL1Converges volume a a₀)
    (ham : ∀ n, Measurable (a n)) (hai : ∀ n, Integrable (a n))
    (heq : ∀ n, f n =ᵐ[μ.prod volume]
      (fun z => a n z.2+Published.timePrimitive μ (r n) z)) :
    g =ᵐ[μ.prod volume] (fun z => a₀ z.2+Published.timePrimitive μ R z) := by
  have hinit := weak_constant_time ham hai ha (μ := μ)
  have hprim := hr.timePrimitive hrm hri
  have hsum := hinit.add hprim
    (fun n => (hai n).comp_snd μ)
    (fun n => Published.timePrimitive_integrable (hrm n) (hri n))
  exact hf.unique (hsum.congr_sequence (fun n => (heq n).symm))

end BoltzmannNonuniqueness.TorusFlight

end

end OAI

import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative

namespace OAI

/-! # Characteristic phase measures and their time-slab increments -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def phaseSlice (F : ℝ × Phase → ℝ) (t : ℝ) : Measure Phase :=
  positiveDensityMeasure volume (fun p => F (t,p))

theorem phaseSlice_finite {F : ℝ × Phase → ℝ} {t : ℝ}
    (hi : Integrable (fun p => F (t,p))) (hn : ∀ᵐ p ∂volume, 0 ≤ F (t,p)) :
    IsFiniteMeasure (phaseSlice F t) := positiveDensityMeasure_finite hi hn

theorem phaseSlice_integral {F : ℝ × Phase → ℝ} {t : ℝ}
    (hm : AEMeasurable (fun p => F (t,p)) volume)
    (hn : ∀ᵐ p ∂volume, 0 ≤ F (t,p)) (φ : Phase → ℝ) :
    (∫ p, φ p ∂phaseSlice F t) = phaseProjection F φ t :=
  positiveDensityMeasure_integral hm hn φ

def phaseIncrement (μ : Measure (ℝ × Phase)) (s t : ℝ) : Measure Phase :=
  (μ.restrict (Prod.fst ⁻¹' Ioc s t)).map Prod.snd

instance phaseIncrement_finite (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ] (s t : ℝ) :
    IsFiniteMeasure (phaseIncrement μ s t) := by unfold phaseIncrement; infer_instance

theorem phaseIncrement_integral (μ : Measure (ℝ × Phase)) (s t : ℝ)
    {φ : Phase → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂phaseIncrement μ s t) =
      ∫ z, (Ioc s t).indicator (fun _ => (1 : ℝ)) z.1*φ z.2 ∂μ := by
  rw [phaseIncrement,integral_map measurable_snd.aemeasurable hφ.aestronglyMeasurable,
    ← integral_indicator (measurable_fst measurableSet_Ioc)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    by_cases hz : z.1 ∈ Ioc s t <;> simp [hz])

theorem phaseIncrement_timeSource (μ : Measure (ℝ × Phase)) (s t : ℝ)
    {φ : Phase → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p) :
    (∫ p, φ p ∂phaseIncrement μ s t) = (timeSource μ φ).real (Ioc s t) := by
  rw [phaseIncrement_integral μ s t hφ,← integral_indicator_one measurableSet_Ioc]
  exact (timeSource_integral μ hφ hn (measurable_const.indicator measurableSet_Ioc)).symm

end BoltzmannNonuniqueness.WeakTime

end

end OAI

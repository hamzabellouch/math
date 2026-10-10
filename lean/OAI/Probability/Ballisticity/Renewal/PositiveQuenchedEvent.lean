import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma integral_lower_test_le_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (hFb : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (A : Set Ω) (hA : MeasurableSet A)
    (hs : ∀ x, F x ≠ 0 → x ∈ A) : (∫ x, F x ∂μ) ≤ μ.real A := by
  rw [← integral_indicator_one hA]
  apply integral_mono_ae
  · exact Integrable.of_bound hF.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (hFb x).1] using (hFb x).2))
  · exact (integrable_const (1:ℝ)).indicator hA
  · exact ae_of_all _ (fun x => by
      by_cases hx : x ∈ A
      · simpa [hx] using (hFb x).2
      · have hz : F x=0 := by contrapose! hx; exact hs x hx
        simp [hx,hz])

lemma event_lower_mass_of_test_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M p : ℕ → Ω → ℝ) (b : ℝ) (hb : 0 < b)
    (hlim : TendstoInMeasure μ M atTop (fun _ => b))
    (hbound : ∀ᶠ i in atTop, ∀ᵐ x ∂μ, M i x ≤ p i x) :
    Tendsto (fun i => μ.real {x | p i x < b/2}) atTop (𝓝 0) := by
  have hh := (tendstoInMeasure_iff_measureReal_norm.mp hlim) (b/2) (half_pos hb)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hh
  filter_upwards [hbound] with i hi
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hi] with x hx
  intro hp
  change p i x < b/2 at hp
  change b/2 ≤ ‖M i x-b‖
  rw [Real.norm_eq_abs,abs_of_nonpos (by linarith : M i x-b ≤ 0)]
  linarith

end DirectionalTransience

end

end

end OAI

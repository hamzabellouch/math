import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma kernel_bounded_integral {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (Q : Kernel Ω G) [IsFiniteKernel Q] (F : G → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (h0 : ∀ u, 0 ≤ F u) (hbound : ∀ u, F u ≤ B)
    (hQ : ∀ ω, Q ω Set.univ ≤ 1) :
    ∀ ω, 0 ≤ (∫ u, F u ∂Q ω) ∧ (∫ u, F u ∂Q ω) ≤ B := by
  intro ω
  have hi : Integrable F (Q ω) := Integrable.of_bound hF.aestronglyMeasurable B
    (Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (h0 u)] using hbound u)
  refine ⟨integral_nonneg h0,?_⟩
  have hh := integral_mono hi (integrable_const B) (fun u => hbound u)
  rw [integral_const,smul_eq_mul] at hh
  apply hh.trans
  have hm : (Q ω).real Set.univ ≤ 1 := by
    simpa only [measureReal_def,ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ∞) (hQ ω)
  exact mul_le_of_le_one_left hB hm

lemma integrable_kernel_bounded_integral {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Q : Kernel Ω G) [IsFiniteKernel Q]
    (F : G → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (h0 : ∀ u, 0 ≤ F u) (hbound : ∀ u, F u ≤ B)
    (hQ : ∀ ω, Q ω Set.univ ≤ 1) :
    Integrable (fun ω => ∫ u, F u ∂Q ω) μ := by
  apply Integrable.of_bound hF.stronglyMeasurable.integral_kernel.aestronglyMeasurable B
  exact Eventually.of_forall fun ω => by
    obtain ⟨h0',hB'⟩ := kernel_bounded_integral Q F hF hB h0 hbound hQ ω
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0'] using hB'

end DirectionalTransience

end

end

end OAI

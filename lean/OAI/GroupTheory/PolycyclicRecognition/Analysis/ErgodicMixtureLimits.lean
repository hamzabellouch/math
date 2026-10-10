import OAI.GroupTheory.PolycyclicRecognition.Analysis.ErgodicDecompositionInput
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace OAI

/-! # Bounded limits through the published ergodic decomposition

Setwise barycenters are enough for the stationary-increment application.
No measurable selection of a label on the components is needed.
-/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

/-- Extend a setwise decomposition to every nonnegative measurable integrand. -/
theorem lintegral_eq_of_setwise_barycenter (μ : Measure X) (κ : X → Measure X)
    (hκ : ∀ s : Set X, MeasurableSet s → Measurable (fun x => κ x s))
    (hbary : ∀ s : Set X, MeasurableSet s → μ s = ∫⁻ x, κ x s ∂μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ y, f y ∂κ x ∂μ := by
  have hm : Measurable κ := Measure.measurable_of_measurable_coe κ hκ
  have heq : μ.bind κ = μ := by
    ext s hs
    rw [Measure.bind_apply hs hm.aemeasurable, ← hbary s hs]
  rw [← heq, Measure.lintegral_bind hm.aemeasurable hf.aemeasurable, heq]

/-- Uniformly bounded componentwise convergence passes through a probability
barycenter, with the component map kept fixed throughout the limit. -/
theorem tendsto_lintegral_of_componentwise_bounded
    (μ : Measure X) [IsProbabilityMeasure μ] (κ : X → Measure X)
    (hκ : ∀ s : Set X, MeasurableSet s → Measurable (fun x => κ x s))
    (hbary : ∀ s : Set X, MeasurableSet s → μ s = ∫⁻ x, κ x s ∂μ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → X → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hbound : ∀ᶠ n in l, ∀ x, ∫⁻ y, f n y ∂κ x ≤ B)
    (hlim : ∀ x, Tendsto (fun n => ∫⁻ y, f n y ∂κ x) l (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ) l (𝓝 0) := by
  have hm : Measurable κ := Measure.measurable_of_measurable_coe κ hκ
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _ : X => B)
    (Eventually.of_forall (fun n => (Measure.measurable_lintegral (hf n)).comp hm))
    (hbound.mono (fun _ hn => Eventually.of_forall hn)) (by simpa using hB)
    (Eventually.of_forall hlim)
  have heq (n : ι) := lintegral_eq_of_setwise_barycenter μ κ hκ hbary (f n) (hf n)
  simpa only [Function.comp_apply, ← heq, lintegral_zero] using h

end PolycyclicRecognition

end OAI

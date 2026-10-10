import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeanProbabilityConverse
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteAffineSelection
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Canonical affine choices for compactly carried sampling laws -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

theorem integrable_continuous_of_ae_mem_compact
    {X E : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] (μ : Measure X) [IsFiniteMeasure μ]
    {C : Set X} (hC : IsCompact C) (hfull : ∀ᵐ x ∂μ, x ∈ C)
    {f : X → E} (hf : Continuous f) : Integrable f μ := by
  have hi := hf.continuousOn.integrableOn_compact (μ := μ) hC
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hfull] at hi

/-- The chosen label depends only on the law and the actual profile,
so different sequences use the same choice at any shared parameter. -/
def canonicalAffineLabel
    {X Y L : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [Finite L] [Nonempty L]
    (μ : Measure X) (f : X → Y) (A : L → Y) : L := by
  letI : Fintype L := Fintype.ofFinite L
  exact minimizingFiniteLabel (fun a => ∫ x, dist (f x) (A a) ∂μ)

theorem canonicalAffineLabel_mean_tendsto_zero
    {X Y L : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [Finite L] [Nonempty L]
    (μ : ℕ → Measure X) (f : ℕ → X → Y) (A : ℕ → L → Y)
    (h : ∃ a : ℕ → L, Tendsto (fun n => ∫ x, dist (f n x) (A n (a n)) ∂μ n)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x,
      dist (f n x) (A n (canonicalAffineLabel (μ n) (f n) (A n))) ∂μ n)
      atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := h
  let : Fintype L := Fintype.ofFinite L
  exact minimizingFiniteLabel_tendsto_zero
    (fun n a => ∫ x, dist (f n x) (A n a) ∂μ n)
    (fun _ _ => integral_nonneg (fun _ => dist_nonneg)) a ha

/-- Compact support supplies the integrability required by Markov's
inequality, including for the canonical minimizing affine label. -/
theorem compact_profile_probability_of_mean
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (C : ℕ → Set X)
    (hC : ∀ n, IsCompact (C n)) (hfull : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x ∈ C n)
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (a : ℕ → Y)
    (hm : Tendsto (fun n => ∫ x, dist (f n x) (a n) ∂(μ n : Measure X)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (μ n : Measure X) {x | ε ≤ dist (f n x) (a n)})
      atTop (𝓝 0) :=
  bad_probability_tendsto_zero_of_mean μ _
    (fun n => integrable_continuous_of_ae_mem_compact (μ n : Measure X) (hC n) (hfull n)
      ((hf n).dist continuous_const))
    (fun _ => Eventually.of_forall (fun _ => dist_nonneg)) hm hε

end PolycyclicRecognition

end

end OAI

import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Independent coordinate changes and their product-volume multiplier -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem measure_pi_smul {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : I → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
    Finset.prod_mul_distrib]

theorem map_pi_of_coordinate_scaling {I : Type*} [Fintype I]
    {X Y : I → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) (ν : ∀ i, Measure (Y i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (f : ∀ i, X i → Y i) (hf : ∀ i, Measurable (f i))
    (c : I → ℝ≥0) (hmap : ∀ i, Measure.map (f i) (μ i) = c i • ν i) :
    Measure.map (fun x i => f i (x i)) (Measure.pi μ) = (∏ i, c i) • Measure.pi ν := by
  let : ∀ i, SigmaFinite (Measure.map (f i) (μ i)) := fun i => by
    rw [hmap i]
    infer_instance
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  simp_rw [hmap]
  exact measure_pi_smul ν c

end PolycyclicRecognition

end

end OAI

import OAI.Probability.InvariantIsing.Fields.FieldQuantizer
import OAI.Probability.InvariantIsing.Spectral.EmpiricalFieldMoment
import OAI.Probability.InvariantIsing.Fields.PhysicalFieldComparison

namespace OAI

/-! Quantization errors are controlled by a first-moment tail, uniformly in the matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace InvariantIsing

lemma fieldBallSimple_integral_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {n : ℕ} (c r : Fin n → ℝ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hc : ∀ i, c i∈Icc (-2*M) (2*M))
    (hr : ∀ i, r i ≤ δ) (hcover : Icc (-2*M) (2*M) ⊆ ⋃ i, Metric.ball (c i) (r i)) :
    (∫ x, |fieldBallSimple c r x-x| ∂μ) ≤ δ+4*(∫ x, fieldTail M x ∂μ) := by
  have hi := integrable_lipschitz_field hμ (fieldTail_lipschitz M)
  calc
    _ ≤ ∫ x, δ+4*fieldTail M x ∂μ := by
      apply integral_mono ((simpleField_integrable μ (fieldBallSimple c r)).sub hμ).abs
        ((integrable_const δ).add (hi.const_mul 4))
      intro x
      exact fieldBallSimple_error c r hM hδ hc hr hcover x
    _ = _ := by rw [integral_add (integrable_const δ) (hi.const_mul 4),integral_const,integral_const_mul]; simp

lemma mean_field_quantizer_error {N n : ℕ} (hN : 0 < N)
    (P : Measure (Orthogonal N)) [IsProbabilityMeasure P] (eig field : Fin N → ℝ)
    (c r : Fin n → ℝ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hc : ∀ i, c i∈Icc (-2*M) (2*M))
    (hr : ∀ i, r i ≤ δ) (hcover : Icc (-2*M) (2*M) ⊆ ⋃ i, Metric.ball (c i) (r i)) :
    |(∫ U, rotatedPressure eig (matrixRotation U⁻¹) field ∂P)-
      ∫ U, rotatedPressure eig (matrixRotation U⁻¹) (fun i => fieldBallSimple c r (field i)) ∂P| ≤
      δ+4*(∫ x, fieldTail M x ∂(empiricalSpectralLaw hN field : Measure ℝ)) := by
  refine (physical_mean_field_l1_le hN P eig field _).trans ?_
  have hh := fieldBallSimple_integral_error (empiricalSpectralLaw hN field : Measure ℝ)
    (empiricalField_integrable hN field id) c r hM hδ hc hr hcover
  rw [empiricalSpectralLaw_integral] at hh
  simpa only [one_div,abs_sub_comm] using hh

end InvariantIsing

end

end OAI

import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Retaining parameter volume on one coordinate slice -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Fubini gives a large section without choosing a measurable family of
representatives for the image of the parameter set. -/
theorem exists_section_measure_gt
    {V Z : Type*} [MeasurableSpace V] [MeasurableSpace Z]
    (μ : Measure V) (ν : Measure Z) [SFinite μ] [SFinite ν]
    {K : Set (V × Z)} (hK : MeasurableSet K)
    {Q : Set Z} (hQ : MeasurableSet Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q) (t : ℝ≥0∞)
    (hmass : t * ν Q < (μ.prod ν) K) :
    ∃ z ∈ Q, t < μ {v | (v, z) ∈ K} := by
  by_contra h
  have hbound (z : Z) : μ {v | (v, z) ∈ K} ≤ Q.indicator (fun _ => t) z := by
    by_cases hz : z ∈ Q
    · rw [indicator_of_mem hz]
      exact le_of_not_gt (fun ht => h ⟨z, hz, ht⟩)
    · have hempty : {v | (v, z) ∈ K} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact hz (hKQ (v, z) hv)
      rw [hempty, measure_empty, indicator_of_notMem hz]
  have he : (μ.prod ν) K ≤ t * ν Q := by
    rw [Measure.prod_apply_symm hK]
    calc
      _ ≤ ∫⁻ z, Q.indicator (fun _ => t) z ∂ν := lintegral_mono hbound
      _ = t * ν Q := by rw [lintegral_indicator hQ]; simp
  exact not_lt_of_ge he hmass

end PolycyclicRecognition

end OAI

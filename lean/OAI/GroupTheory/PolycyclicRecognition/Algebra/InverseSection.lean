import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairCoupling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarProduct

namespace OAI

/-! # The invariant measure on the inverse section

For the actual compact space of quasi-inverse pairs, the Haar coupling in
inverse coordinates factors as a finite nonzero invariant section measure
times Haar measure. No absolute continuity of the section measure is used.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

instance inversePairCoupling_finiteOnCompacts
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts (inversePairCoupling m μ) :=
  Measure.IsFiniteMeasureOnCompacts.map (m.prod μ) pairChartTransition

/-- The product measure remains nonzero under the change of charts. -/
theorem inversePairCoupling_ne_zero
    (m : Measure G) [SFinite m] (hm : m ≠ 0)
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ] :
    inversePairCoupling m μ ≠ 0 := by
  apply (Measure.map_ne_zero_iff pairChartTransition.continuous.measurable.aemeasurable).mpr
  intro h
  apply hm
  apply Measure.measure_univ_eq_zero.mp
  have hu := congrArg (fun ρ : Measure (G × NormalizedPair G Λ) => ρ univ) h
  simpa only [← univ_prod_univ, Measure.prod_prod, measure_univ, mul_one,
    Measure.coe_zero, Pi.zero_apply] using hu

/-- The inverse section has a finite nonzero stationary measure, and its
product with Haar measure is exactly the coupling in inverse coordinates. -/
theorem exists_inverseSection_measure
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] :
    ∃ ν : Measure (NormalizedPair G Λ), IsFiniteMeasure ν ∧ ν ≠ 0 ∧
      SMulInvariantMeasure G (NormalizedPair G Λ) ν ∧
      inversePairCoupling m μ = ν.prod m := by
  obtain ⟨B, hB, hB0⟩ := (Measure.Regular.exists_isCompact_not_null (μ := m)).mpr (NeZero.ne m)
  let M := inversePairCoupling m μ
  let ν := haarSectionMeasure M m B
  have hright := measurePreserving_inversePairCoupling_right m μ
  have hfinite : IsFiniteMeasure ν := haarSectionMeasure_finite M m hB hB0
  let := hfinite
  have hprod : M = ν.prod m := haarProduct_factorization M m hright hB hB0 hB.measure_ne_top
  have hnonzero : ν ≠ 0 := haarSectionMeasure_ne_zero M m hright
    (inversePairCoupling_ne_zero m (NeZero.ne m) μ) hB hB0 hB.measure_ne_top
  refine ⟨ν, hfinite, hnonzero, ?_, hprod⟩
  constructor
  intro g E hE
  have ht := measurePreserving_inversePairCoupling_target m μ g⁻¹
  change MeasurePreserving (pairInverseTargetTranslation g⁻¹) M M at ht
  rw [hprod] at ht
  have hc : Continuous (normalizedTranslate (Λ := Λ) g⁻¹) := by
    have h : Continuous (fun p : NormalizedPair G Λ => g • p) := continuous_const_smul g
    exact h
  have hbase := measurePreserving_base_of_left_skew ν m hc.measurable
    (((continuous_eval_const g⁻¹).comp continuous_subtype_val.fst).inv.measurable)
    ht hB.measurableSet hB0 hB.measure_ne_top
  have hsmul : MeasurePreserving (fun p : NormalizedPair G Λ => g • p) ν ν := hbase
  exact hsmul.measure_preimage hE.nullMeasurableSet

end PolycyclicRecognition

end

end OAI

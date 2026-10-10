import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairCharts
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Translation invariance of the pair coupling

The two commuting translations are written in both product charts. Haar
measure times the stationary probability gives the actual invariant coupling.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

/-- Domain translation, expressed in the target-normalized chart. -/
def pairDomainTranslation (x : G) (q : G × NormalizedPair G Λ) :
    G × NormalizedPair G Λ :=
  (q.1 * q.2.val.1 x, normalizedTranslate x q.2)

/-- Target translation by `y⁻¹`, expressed in the source-normalized chart. -/
def pairInverseTargetTranslation (y : G) (q : NormalizedPair G Λ × G) :
    NormalizedPair G Λ × G :=
  (normalizedTranslate y q.1, (q.1.val.1 y)⁻¹ * q.2)

/-- The transition conjugates domain translation to right translation on the
second coordinate of the inverse chart. -/
theorem pairChartTransition_domain (x : G) (q : G × NormalizedPair G Λ) :
    pairChartTransition (pairDomainTranslation x q) =
      ((pairChartTransition q).1, (pairChartTransition q).2 * x) := by
  rcases q with ⟨z, p⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
    · simp only [pairDomainTranslation, pairChartTransition_forward,
        normalizedTranslate, translatePair, ContinuousMap.coe_mk, mul_inv_rev,
        inv_mul_cancel_left, mul_assoc]
      group
    · simp only [pairDomainTranslation, pairChartTransition_inverse,
        normalizedTranslate, translatePair, ContinuousMap.coe_mk, mul_inv_rev,
        mul_assoc]
      group
  · simp only [pairDomainTranslation, pairChartTransition_group,
      normalizedTranslate, translatePair, ContinuousMap.coe_mk, mul_inv_rev,
      ]
    group

/-- The target action in inverse coordinates is a normalized translation and a
left translation depending on the inverse pair. -/
theorem pairSourceChart_target (y : G) (q : NormalizedPair G Λ × G) :
    pairSourceChart (pairInverseTargetTranslation y q) =
      targetTranslate y⁻¹ (pairSourceChart q) := by
  rcases q with ⟨p, x⟩
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
  · simp only [pairInverseTargetTranslation, pairSourceChart_forward,
      normalizedTranslate, translatePair, ContinuousMap.coe_mk,
      targetTranslate, targetTranslatePair]
    congr 1
    group
  · simp only [pairInverseTargetTranslation, pairSourceChart_inverse,
      normalizedTranslate, translatePair, ContinuousMap.coe_mk,
      targetTranslate, targetTranslatePair]
    group

/-- Target translation in the first chart. -/
theorem pairTargetChart_target (y : G) (q : G × NormalizedPair G Λ) :
    pairTargetChart (y * q.1, q.2) = targetTranslate y (pairTargetChart q) := by
  rcases q with ⟨z, p⟩
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
    simp [pairTargetChart, targetTranslate, targetTranslatePair, mul_assoc]

/-- Target translation conjugated through the change of product charts. -/
theorem pairChartTransition_target (y : G) (q : G × NormalizedPair G Λ) :
    pairChartTransition (y⁻¹ * q.1, q.2) =
      pairInverseTargetTranslation y (pairChartTransition q) := by
  apply pairSourceChart.injective
  rw [pairSourceChart_target]
  change pairSourceChart (pairSourceChart.symm (pairTargetChart (y⁻¹ * q.1, q.2))) =
    targetTranslate y⁻¹ (pairSourceChart (pairSourceChart.symm (pairTargetChart q)))
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, pairTargetChart_target]

variable [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Haar preservation in the target chart follows directly from stationarity
and right invariance of Haar measure. -/
theorem measurePreserving_pairDomainTranslation
    (m : Measure G) [SFinite m] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [SFinite μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (x : G) :
    MeasurePreserving (pairDomainTranslation x) (m.prod μ) (m.prod μ) := by
  have hT : MeasurePreserving (normalizedTranslate x) μ μ := by
    have h := measurePreserving_smul x⁻¹ μ
    change MeasurePreserving (fun p => normalizedTranslate (x⁻¹)⁻¹ p) μ μ at h
    simpa only [inv_inv] using h
  have hskew : MeasurePreserving
      (fun q : NormalizedPair G Λ × G =>
        (normalizedTranslate x q.1, q.2 * q.1.val.1 x))
      (μ.prod m) (μ.prod m) := by
    apply hT.skew_product (g := fun p z => z * p.val.1 x)
    · exact measurable_snd.mul
        (((continuous_eval_const x).comp continuous_fst.subtype_val.fst).measurable)
    · exact Filter.Eventually.of_forall fun p => map_mul_right_eq_self m (p.val.1 x)
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := m)).comp
    (hskew.comp (Measure.measurePreserving_swap (μ := m) (ν := μ)))
  exact h

/-- The coupling measure in inverse coordinates, defined by the actual chart. -/
def inversePairCoupling (m : Measure G) (μ : Measure (NormalizedPair G Λ)) :
    Measure (NormalizedPair G Λ × G) :=
  (m.prod μ).map pairChartTransition

/-- In the inverse chart, the coupling is right invariant in the group fiber. -/
theorem measurePreserving_inversePairCoupling_right
    (m : Measure G) [SFinite m] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [SFinite μ]
    [SMulInvariantMeasure G (NormalizedPair G Λ) μ] (x : G) :
    MeasurePreserving (fun q : NormalizedPair G Λ × G => (q.1, q.2 * x))
      (inversePairCoupling m μ) (inversePairCoupling m μ) := by
  have hmeas : Measurable (fun q : NormalizedPair G Λ × G => (q.1, q.2 * x)) :=
    measurable_fst.prodMk (measurable_snd.mul_const x)
  refine ⟨hmeas, ?_⟩
  unfold inversePairCoupling
  rw [Measure.map_map hmeas pairChartTransition.continuous.measurable]
  have hcomp : (fun q : NormalizedPair G Λ × G => (q.1, q.2 * x)) ∘
      pairChartTransition = pairChartTransition ∘ pairDomainTranslation x := by
    funext q
    exact (pairChartTransition_domain x q).symm
  rw [hcomp, ← Measure.map_map pairChartTransition.continuous.measurable
    (measurePreserving_pairDomainTranslation m μ x).measurable,
    (measurePreserving_pairDomainTranslation m μ x).map_eq]

/-- The same coupling is invariant under the target action in inverse
coordinates. -/
theorem measurePreserving_inversePairCoupling_target
    (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    (μ : Measure (NormalizedPair G Λ)) [SFinite μ] (y : G) :
    MeasurePreserving (pairInverseTargetTranslation y)
      (inversePairCoupling m μ) (inversePairCoupling m μ) := by
  have hmeas : Measurable (pairInverseTargetTranslation (Λ := Λ) y) := by
    apply Measurable.prodMk
    · have hc : Continuous (normalizedTranslate (Λ := Λ) y) := by
        have h : Continuous (fun p : NormalizedPair G Λ => y⁻¹ • p) :=
          continuous_const_smul y⁻¹
        change Continuous (fun p => normalizedTranslate (y⁻¹)⁻¹ p) at h
        simpa only [inv_inv] using h
      exact hc.measurable.comp measurable_fst
    · exact (((continuous_eval_const y).comp
        continuous_fst.subtype_val.fst).measurable.inv).mul measurable_snd
  apply MeasurePreserving.of_semiconj
    (pairChartTransition.continuous.measurable.measurePreserving (m.prod μ))
    ((measurePreserving_mul_left m y⁻¹).prod (MeasurePreserving.id μ))
    (pairChartTransition_target y) hmeas

end PolycyclicRecognition

end

end OAI

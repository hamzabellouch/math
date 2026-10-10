import OAI.GroupTheory.PolycyclicRecognition.Geometry.GenericFlowChambers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.JointFlowRelation

namespace OAI

/-! # The generic chamber relation on the full domain of admissible triples -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter MeasureTheory
open scoped NNReal

theorem ae_generic_joint_chamber_agreement
    {G V W I B L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Countable L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (π : V →L[ℝ] W) (v : V) (hw : ∀ i, D.weight i (π v) ≠ 0)
    (f : G → W) (hf : Continuous f) (U : Set G) (hU : IsOpen U)
    (label : G → L) (hlabel : Measurable label) (A : L → templateSymmetryGroup D)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      ((A (label g)).val (π v)) 0)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ U})
    (hvol : ∀ T : ℝ, 0 < T → ∀ g ∈ flowLineBase U Exp v T,
      T * D.segmentSupport (π v) ≤ D.templateSupport ((fun t : ℝ => f (g * Exp (t • v))) '' Icc 0 T)) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      (A (label (z.2 * Exp (z.1.1 • v)))).val ''
          closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
            (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) =
        (A (label (z.2 * Exp (z.1.2 • v)))).val ''
          closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
            (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) := by
  apply ae_joint_flow_relation_of_intervals μ Exp hExp hadd v U hU label hlabel
    (fun l₁ l₂ => (A l₁).val ''
      closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
        (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) =
      (A l₂).val '' closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
        (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)))
  intro T hT
  exact D.ae_generic_flowLine_chamber_agreement hweights μ Exp hExp hzero hadd π v hw
    f hf U label A hbase hT.le C (fun g hg => (hlip g).mono hg) (hvol T hT)

end PolycyclicRecognition.SupportDatum

end

end OAI

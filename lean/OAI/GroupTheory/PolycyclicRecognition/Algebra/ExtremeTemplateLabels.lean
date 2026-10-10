import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtremeDirectionLabels
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # The actual template labels agree along extreme directions

The positive homogeneous segment-support norm already removes scaling on a
ray. No auxiliary invariant Euclidean norm is a premise of this theorem.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter

theorem extreme_template_derivative_values_equal
    {G V W I B L : Type*}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → L) (hlabel : Measurable label) (A : L → templateSymmetryGroup D)
    (U : Set G) (hU : IsOpen U) (v : V) (σ₀ : I → Bool)
    (hσ₀ : (weightChamber (fun i => (D.weight i).toContinuousLinearMap) σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap) σ₀)
      (nonnegativeRay (π v)))
    (hgeneric : ∀ σ : I → Bool,
      incidentWeightChamber (fun i => (D.weight i).toContinuousLinearMap) (π v) σ →
      ∀ u : V, π u ∈ weightChamber (fun i => (D.weight i).toContinuousLinearMap) σ →
      ∀ᵐ z ∂(pairTimeMeasure.prod μ), z ∈ flowSegmentDomain U Exp u →
        (A (label (z.2 * Exp (z.1.1 • u)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap) σ =
          (A (label (z.2 * Exp (z.1.2 • u)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap) σ) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      (A (label (z.2 * Exp (z.1.1 • v)))).val (π v) =
        (A (label (z.2 * Exp (z.1.2 • v)))).val (π v) := by
  let α : I → W →L[ℝ] ℝ := fun i => (D.weight i).toContinuousLinearMap
  have hα (i : I) : α i ≠ 0 := by
    intro hi
    apply hweights i
    ext w
    exact congrArg (fun f : W →L[ℝ] ℝ => f w) hi
  apply ae_restrict_of_compact_subsets (pairTimeMeasure.prod μ)
    (flowSegmentDomain U Exp v) (isOpen_flowSegmentDomain U hU Exp hExp v)
  intro K hK hKU
  filter_upwards [direction_chambers_agree_on_compact μ π hπ Exp hExp label hlabel
    (fun l => (A l).val) α U hU v hgeneric K hK hKU] with z hz
  exact eq_on_extreme_ray_of_incident_chambers_of_gauge α hα D.separates σ₀ hσ₀ hExt
    D.segmentSupport (fun _ hw => D.segmentSupport_pos hw)
    (fun w _ hr => D.segmentSupport_smul_of_nonneg w hr) _ _
    (templateSymmetry_mem_linearSupportSymmetry D (A _) (π v))
    (templateSymmetry_mem_linearSupportSymmetry D (A _) (π v)) hz

end PolycyclicRecognition.SupportDatum

end

end OAI

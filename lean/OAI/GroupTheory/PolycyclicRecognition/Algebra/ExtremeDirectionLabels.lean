import OAI.GroupTheory.PolycyclicRecognition.Algebra.JointDirectionLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactFlowSegments
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightChamberLimits
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactAeExhaustion

namespace OAI

/-! # Constant labels on extreme horizontal directions

The generic chamber relation passes through actual approximating horizontal
vectors, jointly in the base point and both times. The incident chambers
then determine the extreme ray and its norm-preserving label value.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

variable {G V W I L : Type*}
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Finite I]
  [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]

omit [FiniteDimensional ℝ W] in
theorem direction_chambers_agree_on_compact
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → L) (hlabel : Measurable label)
    (A : L → W ≃ₗ[ℝ] W) (α : I → W →L[ℝ] ℝ)
    (U : Set G) (hU : IsOpen U) (v : V)
    (hgeneric : ∀ σ : I → Bool, incidentWeightChamber α (π v) σ →
      ∀ u : V, π u ∈ weightChamber α σ →
      ∀ᵐ z ∂(pairTimeMeasure.prod μ), z ∈ flowSegmentDomain U Exp u →
        A (label (z.2 * Exp (z.1.1 • u))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • u))) '' closedWeightChamber α σ)
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K)
    (hKU : K ⊆ flowSegmentDomain U Exp v) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      ∀ σ, incidentWeightChamber α (π v) σ →
        A (label (z.2 * Exp (z.1.1 • v))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • v))) '' closedWeightChamber α σ := by
  have hchamber (σ : I → Bool) : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      incidentWeightChamber α (π v) σ →
        A (label (z.2 * Exp (z.1.1 • v))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • v))) '' closedWeightChamber α σ := by
    by_cases hs : incidentWeightChamber α (π v) σ
    · obtain ⟨u, hu, huc⟩ := exists_lifted_chamber_sequence π hπ α v σ hs
      have hstay := eventually_compact_flowSegments U hU Exp hExp u hu K hK hKU
      have hevent : ∀ᶠ n in atTop, ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
          A (label (z.2 * Exp (z.1.1 • u n))) '' closedWeightChamber α σ =
            A (label (z.2 * Exp (z.1.2 • u n))) '' closedWeightChamber α σ := by
        filter_upwards [hstay] with n hn
        filter_upwards [ae_restrict_of_ae (hgeneric σ hs (u n) (huc n)),
          ae_restrict_mem hK.measurableSet] with z hz hzk
        exact hz (hn hzk)
      have he := finiteLabel_jointDirections_relation μ Exp hExp label hlabel u hu K hK
        (fun l m => A l '' closedWeightChamber α σ = A m '' closedWeightChamber α σ) hevent
      exact he.mono (fun _ hz _ => hz)
    · exact Eventually.of_forall (fun _ h => (hs h).elim)
  exact ae_all_iff.mpr hchamber

theorem extreme_direction_labels_equal_on_compact
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → L) (hlabel : Measurable label)
    (A : L → W ≃ₗ[ℝ] W) (hA : ∀ l w, ‖A l w‖ = ‖w‖)
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    (U : Set G) (hU : IsOpen U) (v : V) (σ₀ : I → Bool)
    (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay (π v)))
    (hgeneric : ∀ σ : I → Bool, incidentWeightChamber α (π v) σ →
      ∀ u : V, π u ∈ weightChamber α σ →
      ∀ᵐ z ∂(pairTimeMeasure.prod μ), z ∈ flowSegmentDomain U Exp u →
        A (label (z.2 * Exp (z.1.1 • u))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • u))) '' closedWeightChamber α σ)
    (K : Set ((ℝ × ℝ) × G)) (hK : IsCompact K)
    (hKU : K ⊆ flowSegmentDomain U Exp v) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict K,
      A (label (z.2 * Exp (z.1.1 • v))) (π v) =
        A (label (z.2 * Exp (z.1.2 • v))) (π v) := by
  filter_upwards [direction_chambers_agree_on_compact μ π hπ Exp hExp label hlabel A
    α U hU v hgeneric K hK hKU] with z hz
  exact eq_on_extreme_ray_of_incident_chambers α hα hsep σ₀ hσ₀ hExt _ _
    (hA _) (hA _) hz

/-- Exhaustion removes the compact carrier; the exceptional set is null on
the full open domain of admissible flow triples. -/
theorem extreme_direction_labels_equal
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (Exp : V → G) (hExp : Continuous Exp)
    (label : G → L) (hlabel : Measurable label)
    (A : L → W ≃ₗ[ℝ] W) (hA : ∀ l w, ‖A l w‖ = ‖w‖)
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    (U : Set G) (hU : IsOpen U) (v : V) (σ₀ : I → Bool)
    (hσ₀ : (weightChamber α σ₀).Nonempty)
    (hExt : IsExtreme ℝ (closedWeightChamber α σ₀) (nonnegativeRay (π v)))
    (hgeneric : ∀ σ : I → Bool, incidentWeightChamber α (π v) σ →
      ∀ u : V, π u ∈ weightChamber α σ →
      ∀ᵐ z ∂(pairTimeMeasure.prod μ), z ∈ flowSegmentDomain U Exp u →
        A (label (z.2 * Exp (z.1.1 • u))) '' closedWeightChamber α σ =
          A (label (z.2 * Exp (z.1.2 • u))) '' closedWeightChamber α σ) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      A (label (z.2 * Exp (z.1.1 • v))) (π v) =
        A (label (z.2 * Exp (z.1.2 • v))) (π v) := by
  apply ae_restrict_of_compact_subsets (pairTimeMeasure.prod μ)
    (flowSegmentDomain U Exp v) (isOpen_flowSegmentDomain U hU Exp hExp v)
  intro K hK hKU
  exact extreme_direction_labels_equal_on_compact μ π hπ Exp hExp label hlabel A hA
    α hα hsep U hU v σ₀ hσ₀ hExt hgeneric K hK hKU

end PolycyclicRecognition

end

end OAI

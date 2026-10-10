import OAI.GroupTheory.PolycyclicRecognition.Algebra.GenericJointChambers
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtremeTemplateLabels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteFlowSlopes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChamberExtremeDirections

namespace OAI

/-! # Affine restrictions in kernel and extreme horizontal directions -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter MeasureTheory
open scoped NNReal

theorem flowLine_affine_in_extreme_or_kernel_direction
    {G V W I B L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (f : G → W) (hf : Continuous f) (U : Set G) (hU : IsOpen U)
    (label : G → L) (hlabel : Measurable label) (A : L → templateSymmetryGroup D)
    (hbase : ∀ v, ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      ((A (label g)).val (π v)) 0)
    (C : V → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ U})
    (hvol : ∀ v (T : ℝ), 0 < T → ∀ g ∈ flowLineBase U Exp v T,
      T * D.segmentSupport (π v) ≤ D.templateSupport ((fun t : ℝ => f (g * Exp (t • v))) '' Icc 0 T))
    (σ : I → Bool) (hσ : (weightChamber (fun i => (D.weight i).toContinuousLinearMap) σ).Nonempty)
    (v : V) (hv : π v = 0 ∨ π v ∈ chamberExtremeDirections
      (fun i => (D.weight i).toContinuousLinearMap) σ)
    {T : ℝ} (hT : 0 < T) :
    ∀ g ∈ flowLineBase U Exp v T, ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g := by
  let q : G → W := fun g => (A (label g)).val (π v)
  have hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v)) := by
    rcases hv with hv | hv
    · exact Eventually.of_forall (fun _ => by simp [q, hv])
    · apply D.extreme_template_derivative_values_equal hweights μ π hπ Exp hExp
        label hlabel A U hU v σ hσ hv.2
      intro τ _ u hu
      have hw := generic_of_mem_weightChamber
        (fun i => (D.weight i).toContinuousLinearMap) hu
      have he := weightSigns_eq_of_mem_chamber
        (fun i => (D.weight i).toContinuousLinearMap) hu
      have hh := ae_imp_of_ae_restrict (D.ae_generic_joint_chamber_agreement hweights μ
        Exp hExp hzero hadd π u hw f hf U hU label hlabel A (hbase u)
        (C u) (hlip u) (hvol u))
      simpa only [he] using hh
  exact (finite_flowLine_slopes μ Exp hExp hzero v U hU f q hf.continuousOn
    (fun i => (D.weight i).toContinuousLinearMap) D.separates hT
    (fun g hg => (hlip v g).mono hg)
    (ae_flowLine_hasDerivAt_of_ae_base μ Exp hExp hadd v f q U (hbase v) T)
    hpair (Set.finite_range (fun l => (A l).val (π v)))
    (fun g _ => ⟨label g, rfl⟩)).1

end PolycyclicRecognition.SupportDatum

end

end OAI

import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ActivationSaturationBounds
import OAI.Geometry.TamingCompatibility.Currents.CutoffEquation
import OAI.Geometry.TamingCompatibility.DifferentialForms.SummableRestriction

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2
variable (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
  (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)

lemma concentration_restriction_closed
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (θ : smoothForms X 1) :
    unitMeasureCurrent J (hermitianMetric J α hs ht)
      (μ.restrict ((fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' exceptional S.cutoff))
      ⟨exteriorDerivative θ.val,θ.property.exteriorDerivative⟩ = 0 := by
  let c := fun n (u : MetricUnit (hermitianMetric J α hs ht)) => S.cutoff n u.val.proj
  let a := fun u : MetricUnit (hermitianMetric J α hs ht) =>
    eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)
  let b := fun x => ⟪l2Coefficients A J α hs ht E hE Q x,
    normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫
  have ha : Integrable a μ :=
    (smoothUnitEvaluation J (hermitianMetric J α hs ht)
      ⟨_,θ.property.exteriorDerivative⟩).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : Integrable b (geometricVolume A J α) :=
    coefficient_pairing_integrable A J α hs ht E hE Q ⟨_,θ.property.exteriorDerivative⟩
  have hπ : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  obtain ⟨CP,hCP,hP⟩ := saturation_unit_boundary A J α hs ht E hE μ Q S θ
  obtain ⟨CQ,hCQ,hQ⟩ := saturation_Q_boundary A J α hs ht E hE μ Q S θ
  have hh := restriction_zero_of_tail_bounds c S.cutoff
    (fun n u => S.nonneg n u.val.proj) S.nonneg
    (fun n => ((S.smooth n).continuous.comp hπ).measurable)
    (fun n => (S.smooth n).continuous.measurable)
    μ (geometricVolume A J α) a b ha hb S.null
    (fun n => (CP+CQ)*stepSize n) (fun n => mul_nonneg (add_nonneg hCP hCQ) (stepSize_pos n).le)
    (summable_stepSize.mul_left _) (fun n N => ?_)
  · exact hh
  · apply (current_cutoff_bound A J α hs ht E hE μ Q hT
      (saturation S.cutoff n N) (contMDiff_saturation S.smooth n N) θ).trans
    apply (add_le_add (hP n N) (hQ n N)).trans_eq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI

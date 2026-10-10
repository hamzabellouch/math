import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationRestriction
import OAI.Geometry.TamingCompatibility.Hodge.HodgeL2

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

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitMeasureCurrent_restrict_add
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Z : Set (MetricUnit (hermitianMetric J α hs ht))) (hZ : MeasurableSet Z)
    (a : smoothForms X 2) :
    unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Z) a+
      unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Zᶜ) a =
        unitMeasureCurrent J (hermitianMetric J α hs ht) μ a := by
  have hi := (smoothUnitEvaluation J (hermitianMetric J α hs ht) a).continuous.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  change (∫ u, smoothUnitEvaluation J (hermitianMetric J α hs ht) a u ∂μ.restrict Z)+
      (∫ u, smoothUnitEvaluation J (hermitianMetric J α hs ht) a u ∂μ.restrict Zᶜ) = _
  rw [← integral_add_measure hi.restrict hi.restrict,Measure.restrict_add_restrict_compl hZ]
  rfl

lemma concentration_residual_source_closed
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    let ν := μ.restrict ((fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' (exceptional S.cutoff)ᶜ)
    ∀ ξ : PreL2 A J α hs ht false,
      (positiveL2Source A J α hs ht ν + l2CurrentSource A J α hs ht Q)
        (hodgePreD A J α hs ht ξ) = 0 := by
  dsimp only
  let Z := (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' exceptional S.cutoff
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hZ : MeasurableSet Z :=
    (measurable_exceptional S.cutoff S.nonneg (fun n => (S.smooth n).continuous.measurable)).preimage hp.measurable
  intro ξ
  have hclosed := concentration_restriction_closed A J α hs ht E hE μ Q S hT ξ
  have hsplit := unitMeasureCurrent_restrict_add J α hs ht μ Z hZ (hodgePreD A J α hs ht ξ)
  have ht' := hT (hodgePreD A J α hs ht ξ) ξ.property.closed_exteriorDerivative
  change unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Z) (hodgePreD A J α hs ht ξ) = 0 at hclosed
  rw [hclosed,zero_add] at hsplit
  change unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Zᶜ) (hodgePreD A J α hs ht ξ)+
    ⟪Q,smoothL2 A J α hs ht true (hodgePreD A J α hs ht ξ)⟫ = 0
  rw [hsplit]
  exact ht'
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI

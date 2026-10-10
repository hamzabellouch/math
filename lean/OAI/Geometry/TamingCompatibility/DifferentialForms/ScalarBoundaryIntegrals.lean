import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeL2Coefficients

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

omit [IsManifold Model ∞ X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma smooth_boundary (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    IsSmooth (ManifoldForms.wedgeOne (scalarDifferential f) θ.val) :=
  (scalarDifferential_smooth hf).wedgeOne θ.property

omit [MeasurableSpace X] [BorelSpace X] in
lemma unit_boundary_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      |eval (ManifoldForms.wedgeOne (scalarDifferential f) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)|) μ :=
  (smoothUnitEvaluation J (hermitianMetric J α hs ht)
    ⟨_,smooth_boundary f hf θ⟩).continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hE in
lemma coefficient_boundary_integrable
    (Q : L2 A J α hs ht true) (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (θ : smoothForms X 1) :
    Integrable (fun x => ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ.val x)‖)
      (geometricVolume A J α) := by
  let q := l2Coefficients A J α hs ht E hE Q
  have hb := smoothFrameEncode_memLp A J α hs ht E hE ⟨_,smooth_boundary f hf θ⟩
  exact (Lp.memLp q).norm.integrable_mul hb.norm

include hE in
lemma coefficient_pairing_integrable (Q : L2 A J α hs ht true) (a : smoothForms X 2) :
    Integrable (fun x => ⟪l2Coefficients A J α hs ht E hE Q x,
      normalizedFrameEncode A J α ht E x (a.val x)⟫) (geometricVolume A J α) := by
  apply (MeasureTheory.L2.integrable_inner
    (l2Coefficients A J α hs ht E hE Q)
    (l2Coefficients A J α hs ht E hE (smoothL2 A J α hs ht true a))).congr
  filter_upwards [l2Coefficients_smooth A J α hs ht E hE a] with x hx
  rw [hx]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI

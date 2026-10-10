import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarBoundaryIntegrals

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

lemma current_cutoff_equation
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    (∫ u : MetricUnit (hermitianMetric J α hs ht), f u.val.proj *
      eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) ∂μ) +
      (∫ x, f x * ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫ ∂geometricVolume A J α) =
      -(unitMeasureCurrent J (hermitianMetric J α hs ht) μ ⟨_,smooth_boundary f hf θ⟩ +
        ⟪Q,smoothL2 A J α hs ht true ⟨_,smooth_boundary f hf θ⟩⟫) := by
  let a : smoothForms X 2 := ⟨fun x => f x • exteriorDerivative θ.val x, θ.property.exteriorDerivative.fun_smul hf⟩
  let b : smoothForms X 2 := ⟨_,smooth_boundary f hf θ⟩
  have hb : a+b = ⟨exteriorDerivative (fun x => f x • θ.val x),
      (θ.property.fun_smul hf).exteriorDerivative⟩ := by
    apply Subtype.ext
    exact (exteriorDerivative_fun_smul hf θ.property).symm
  have h := hT (a+b) (by rw [hb]; exact (θ.property.fun_smul hf).closed_exteriorDerivative)
  erw [_root_.map_add,_root_.map_add,inner_add_right] at h
  have haP : unitMeasureCurrent J (hermitianMetric J α hs ht) μ a =
      ∫ u : MetricUnit (hermitianMetric J α hs ht), f u.val.proj *
        eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) ∂μ := by
    rfl
  have haQ : ⟪Q,smoothL2 A J α hs ht true a⟫ =
      ∫ x, f x * ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫ ∂geometricVolume A J α := by
    rw [l2Coefficients_pairing A J α hs ht E hE Q a]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change ⟪_,normalizedFrameEncode A J α ht E x (f x • exteriorDerivative θ.val x)⟫ = _
    erw [_root_.map_smul]
    rw [real_inner_smul_right]
  rw [haP,haQ] at h
  change _ = -(unitMeasureCurrent J (hermitianMetric J α hs ht) μ b + ⟪Q,smoothL2 A J α hs ht true b⟫)
  linarith

lemma current_cutoff_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    |(∫ u : MetricUnit (hermitianMetric J α hs ht), f u.val.proj *
      eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) ∂μ) +
      (∫ x, f x * ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫ ∂geometricVolume A J α)| ≤
      (∫ u : MetricUnit (hermitianMetric J α hs ht),
        |eval (ManifoldForms.wedgeOne (scalarDifferential f) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ) +
      (∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ.val x)‖ ∂geometricVolume A J α) := by
  rw [current_cutoff_equation A J α hs ht E hE μ Q hT f hf θ,abs_neg]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact abs_integral_le_integral_abs
  · rw [l2Coefficients_pairing A J α hs ht E hE Q ⟨_,smooth_boundary f hf θ⟩]
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono (coefficient_pairing_integrable A J α hs ht E hE Q ⟨_,smooth_boundary f hf θ⟩).abs
      (coefficient_boundary_integrable A J α hs ht E hE Q f hf θ)
    exact fun x => abs_real_inner_le_norm _ _
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI

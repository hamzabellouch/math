import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothingKernel
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatSmoothing

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeSpectralHeat_symmetric (t : ℝ) (f g : L2 A J α hs ht true) :
    ⟪hodgeSpectralHeat A J α hs ht D hD t f,g⟫ =
      ⟪f,hodgeSpectralHeat A J α hs ht D hD t g⟫ := by
  exact hodgeBoundedSpectralMultiplier_symmetric A J α hs ht D hD
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x)) f g

lemma hodgeSpectralHeat_doubled_inner (t : ℝ) (ht' : 0 ≤ t) (f g : L2 A J α hs ht true) :
    ⟪f,hodgeSpectralHeat A J α hs ht D hD (t+t) g⟫ =
      ⟪hodgeSpectralHeat A J α hs ht D hD t f,hodgeSpectralHeat A J α hs ht D hD t g⟫ := by
  rw [hodgeSpectralHeat_add A J α hs ht D hD t t ht' ht', mul_apply_eq_comp,
    hodgeSpectralHeat_symmetric]

variable [T2Space X]
variable {A J α hs ht D hD}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def heatEvaluation (u : MetricUnit g) : L2 A J α hs ht true →L[ℝ] ℝ :=
  (C.evaluation g u).comp (hodgeHeatBoost A J α hs ht D hD r)

lemma heatEvaluation_continuous : Continuous (C.heatEvaluation g) :=
  (C.evaluation_continuous g).clm_comp continuous_const

lemma heatEvaluation_smooth (u : MetricUnit g) (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true)
    (ha : hodgeSpectralHeat A J α hs ht D hD (r^2) f = smoothL2 A J α hs ht true a) :
    C.heatEvaluation g u f = unitEvaluation J g a.val a.property u := by
  apply C.evaluation_smooth g u _ a
  have he := congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f)
    (hodgeSpectralHeat_factor A J α hs ht D hD r hr)
  exact he.symm.trans ha

def heatEvaluationVector (u : MetricUnit g) : L2 A J α hs ht true :=
  (C.heatEvaluation g u).adjoint 1

lemma heatEvaluationVector_continuous : Continuous (C.heatEvaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.heatEvaluation_continuous g)).clm_apply continuous_const

lemma heatEvaluationVector_integrable (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    Integrable (C.heatEvaluationVector g) μ :=
  (C.heatEvaluationVector_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def heatRegularize (μ : Measure (MetricUnit g)) : L2 A J α hs ht true :=
  ∫ u, C.heatEvaluationVector g u ∂μ

lemma heatRegularize_pair (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (f : L2 A J α hs ht true) :
    ⟪C.heatRegularize g μ,f⟫ = ∫ u, C.heatEvaluation g u f ∂μ := by
  have h := HilbertKernel.regularize_pair μ (C.heatEvaluation g) (fun _ => (1:ℝ))
    (C.heatEvaluationVector_integrable g μ) f
  simpa only [HilbertKernel.regularize,heatRegularize,heatEvaluationVector,
    Real.inner_apply,one_mul,mul_one] using h

def heatInnerKernel (u v : MetricUnit g) : ℝ :=
  ⟪C.heatEvaluationVector g u,C.heatEvaluationVector g v⟫

lemma heatInnerKernel_continuous :
    Continuous (fun p : MetricUnit g × MetricUnit g => C.heatInnerKernel g p.1 p.2) :=
  ((C.heatEvaluationVector_continuous g).comp continuous_fst).inner
    ((C.heatEvaluationVector_continuous g).comp continuous_snd)

lemma heatRegularize_inner (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.heatRegularize g μ,C.heatRegularize g ν⟫ =
      ∫ u, ∫ v, C.heatInnerKernel g u v ∂ν ∂μ := by
  have h := HilbertKernel.regularize_kernel_pair μ ν (C.heatEvaluation g) (C.heatEvaluation g)
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (C.heatEvaluationVector_integrable g μ) (C.heatEvaluationVector_integrable g ν)
  simpa only [heatRegularize,HilbertKernel.regularize,heatInnerKernel,heatEvaluationVector,
    HilbertKernel.kernel_inner] using h

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end

end OAI

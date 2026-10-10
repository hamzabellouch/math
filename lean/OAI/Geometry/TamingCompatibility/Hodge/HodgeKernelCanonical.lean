import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeRegularization
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalSmooth

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
lemma gram_positive_definite {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {ι : Type*} (s : Finset ι) (v : ι → H) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*⟪v i,v j⟫ := by
  have h := real_inner_self_nonneg (x := ∑ i ∈ s, c i • v i)
  simpa only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    mul_assoc,mul_left_comm,mul_comm,real_inner_comm] using h

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source}
  {D' : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD' : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D' p).source}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (C' : HodgeSmoothingCover A J α hs ht D' hD' r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluation_eq (u : MetricUnit g) : C.evaluation g u = C'.evaluation g u := by
  have he : (fun f => C.evaluation g u f) = (fun f => C'.evaluation g u f) :=
    (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).equalizer
      (C.evaluation g u).continuous (C'.evaluation g u).continuous (by
        funext a
        dsimp only [Function.comp_apply]
        exact (C.evaluation_smooth g u _ a
          (hodgeRegularization_smoothShift_cube A J α hs ht r hr a)).trans
          (C'.evaluation_smooth g u _ a
            (hodgeRegularization_smoothShift_cube A J α hs ht r hr a)).symm)
  ext f
  exact congrFun he f

lemma evaluationVector_eq (u : MetricUnit g) : C.evaluationVector g u = C'.evaluationVector g u := by
  unfold evaluationVector
  rw [C.evaluation_eq C' g u]

lemma innerKernel_eq (u v : MetricUnit g) : C.innerKernel g u v = C'.innerKernel g u v := by
  unfold innerKernel
  rw [C.evaluationVector_eq C' g u,C.evaluationVector_eq C' g v]

lemma wedgeKernel_eq (u v : MetricUnit g) : C.wedgeKernel g u v = C'.wedgeKernel g u v := by
  unfold wedgeKernel
  rw [C.evaluationVector_eq C' g u,C.evaluationVector_eq C' g v]

lemma regularize_eq (μ : Measure (MetricUnit g)) : C.regularize g μ = C'.regularize g μ := by
  unfold regularize
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (C.evaluationVector_eq C' g)

lemma innerKernel_symm (u v : MetricUnit g) : C.innerKernel g u v = C.innerKernel g v u :=
  real_inner_comm _ _

lemma wedgeKernel_symm (u v : MetricUnit g) : C.wedgeKernel g u v = C.wedgeKernel g v u := by
  unfold wedgeKernel
  rw [← l2Star_self_adjoint,real_inner_comm]

lemma innerKernel_positive_definite {ι : Type*} (s : Finset ι)
    (u : ι → MetricUnit g) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i*c j*C.innerKernel g (u i) (u j) := by
  exact gram_positive_definite s (fun i => C.evaluationVector g (u i)) c
end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end

end OAI

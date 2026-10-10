import OAI.Geometry.RCD.Metric.HamiltonJacobiDensity
import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! # The Hamilton--Jacobi bound on a compressed geodesic plan

The actual squared gradient inequality implies the sharp quadratic
transport-action bound, at each time and on the same interior region.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem hamilton_jacobi_plan_bound (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hLength : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u : SobolevSpace μ Q) (D : Lp ℝ 2 μ) (t : Time)
    {S : Set X} (hS : MeasurableSet S) (hs : ∀ᵐ γ ∂π, γ t ∈ S)
    (hbound : ∀ᵐ x ∂μ.restrict S, (SobolevSpace.minimalSlope μ Q u x)^2 ≤ 2*D x) :
    -(∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/2 ≤
      (∫ γ : C(Time,X), D (γ t) ∂π) -
        ∫ γ : C(Time,X), dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q u (γ t) ∂π := by
  have hDm : MemLp (fun γ : C(Time,X) => D (γ t)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) D
  have hGm : MemLp (fun γ : C(Time,X) => SobolevSpace.minimalSlope μ Q u (γ t)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t)
      (SobolevSpace.minimalSlope μ Q u)
  have hB : ∀ᵐ γ ∂π, (SobolevSpace.minimalSlope μ Q u (γ t))^2 ≤ 2*D (γ t) := by
    have hx := (ae_restrict_iff' hS).mp hbound
    have hy := ae_of_ae_map (measurable_path_eval t).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp t)).ae_le hx)
    filter_upwards [hy,hs] with γ hγ hsγ
    exact hγ hsγ
  have hiD := hDm.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hiG : Integrable (fun γ : C(Time,X) =>
      dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q u (γ t)) π :=
    hLength.integrable_mul hGm
  have hi := integral_mono_ae (hLength.integrable_sq.neg.div_const 2) (hiD.sub hiG)
    (hB.mono fun γ hγ => by
      have hsq := sq_nonneg (SobolevSpace.minimalSlope μ Q u (γ t)-dist (γ 0) (γ 1))
      change -(dist (γ 0) (γ 1))^2/2 ≤ D (γ t)-
        dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q u (γ t)
      nlinarith)
  simp only [Pi.neg_apply,Pi.sub_apply,integral_div,integral_neg] at hi
  change -(∫ γ : C(Time,X), (dist (γ 0) (γ 1))^2 ∂π)/2 ≤
    ∫ γ : C(Time,X), D (γ t)-dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q u (γ t) ∂π at hi
  rw [integral_sub hiD hiG] at hi
  exact hi

end RegularPointCoordinates

end

end OAI

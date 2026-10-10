import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.SpatialHeat
import OAI.Geometry.WeakHessian.Calculus.LipschitzPointLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile144
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] in
lemma exists_lipschitz_integral [IsLocallyFiniteMeasure m] [IsUnifLocDoublingMeasure m]
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {T : Type*} [MeasurableSpace T] {μ : Measure T}
    {us : T → Lp ℝ 2 m} (hu : Integrable us μ) {cs : T → ℝ≥0}
    (hc : Integrable (fun t => (cs t:ℝ)) μ)
    (hLip : ∀ᵐ t ∂μ,∃ g : X → ℝ,LipschitzWith (cs t) g ∧ g =ᵐ[m] us t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (∫ t,(cs t:ℝ) ∂μ)) g ∧ g =ᵐ[m] ((∫ t,us t ∂μ) : Lp ℝ 2 m) := by
  apply exists_lipschitz_of_ball_averages
  intro x y r hr
  have hm (x : X) : m (Metric.closedBall x r) ≠ ∞ := (hfin _ Metric.isBounded_closedBall).ne
  have hp (x : X) : m (Metric.closedBall x r) ≠ 0 := ne_of_gt
    ((hfull _ Metric.isOpen_ball ⟨x,Metric.mem_ball_self hr⟩).trans_le (measure_mono Metric.ball_subset_closedBall))
  let q (x : X) := setDensity (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hqi (x : X) := setDensity_integrable (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hqn (x : X) := setDensity_nonneg (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x)
  have hqm (x : X) := setDensity_mass (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x) (hp x)
  have hqs (x : X) := setDensity_supported (Metric.closedBall x r) Metric.isClosed_closedBall.measurableSet (hm x) x (Subset.refl _)
  have heq (v : Lp ℝ 2 m) (x : X) : ⟪v,q x⟫_ℝ = (⨍ z in Metric.closedBall x r,v z ∂m) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply,conj_trivial]
    rw [setDensity_pairing,setAverage_eq,measureReal_def,smul_eq_mul]
  let w := q x-q y
  have hpoint : ∀ᵐ t ∂μ,|⟪w,us t⟫_ℝ| ≤ (cs t:ℝ)*(2*r+dist x y) := by
    filter_upwards [hLip] with t ht
    obtain ⟨g,hg,he⟩ := ht
    have Hx := lipschitz_point_pairing_bound hg (us t) (q x) he (hqi x) (hqn x) (hqm x) x hr.le (hqs x)
    have Hy := lipschitz_point_pairing_bound hg (us t) (q y) he (hqi y) (hqn y) (hqm y) y hr.le (hqs y)
    have Hxy := hg.dist_le_mul x y
    rw [Real.dist_eq] at Hxy
    rw [real_inner_comm,show w=q x-q y from rfl,inner_sub_right]
    have H1 := abs_sub_le ⟪us t,q x⟫_ℝ (g x) ⟪us t,q y⟫_ℝ
    have H2 := abs_sub_le (g x) (g y) ⟪us t,q y⟫_ℝ
    rw [abs_sub_comm ⟪us t,q x⟫_ℝ (g x)] at H1
    nlinarith only [H1,H2,Hx,Hy,Hxy]
  have hi : Integrable (fun t => ⟪w,us t⟫_ℝ) μ := (innerSL ℝ w).integrable_comp hu
  have HB : |∫ t,⟪w,us t⟫_ℝ ∂μ| ≤ (∫ t,(cs t:ℝ) ∂μ)*(2*r+dist x y) := by
    calc
      _ ≤ ∫ t,|⟪w,us t⟫_ℝ| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ t,(cs t:ℝ)*(2*r+dist x y) ∂μ := integral_mono_ae hi.norm (hc.mul_const _) hpoint
      _ = _ := integral_mul_const _ _
  have HH := (innerSL ℝ w).integral_comp_comm hu
  change (∫ t,⟪w,us t⟫_ℝ ∂μ) = ⟪w,(∫ t,us t ∂μ)⟫_ℝ at HH
  rw [HH] at HB
  change |⟪w,(∫ t,us t ∂μ)⟫_ℝ| ≤ _ at HB
  rw [real_inner_comm,show w=q x-q y from rfl,inner_sub_right,heq _ x,heq _ y] at HB
  simpa only [Real.coe_toNNReal _ (integral_nonneg fun t => (cs t).coe_nonneg)] using HB
end WeakHessian

end
end InlinedFile144

end OAI

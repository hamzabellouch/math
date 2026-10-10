import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.MinNatTendsto

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_davies {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB (cheegerHeat h t u)‖^2 ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  have hd : Dense (Q.resolventLinear.toLinearMap.range : Set (Lp ℝ 2 m)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (Q.resolvent_range_dense (cheeger_domain_dense h))
  apply hd.induction (P := fun v => ‖T (cheegerHeat h t v)‖^2 ≤ ‖T v‖^2*Real.exp (2*(L:ℝ)^2*t)) ?_ ?_ u
  · rintro v ⟨w,rfl⟩
    exact hcd.cheegerHeat_davies_generator hfinite o h (Q.isFormGenerator_resolvent w) hV hB ht
  · exact isClosed_le ((T.continuous.comp (cheegerHeat h t).continuous).norm.pow 2)
      ((T.continuous.norm.pow 2).mul_const _)

lemma CurvatureDimension.cheegerHeat_weighted {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (fun x => cheegerHeat h t u x*Real.exp (V x)) 2 m ∧
      (∫ x, (cheegerHeat h t u x*Real.exp (V x))^2 ∂m) ≤
        ‖hU.toLp (fun x => u x*Real.exp (V x))‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  apply memLp_mul_exp_of_trunc hV.continuous.aestronglyMeasurable
  intro n
  have H := hcd.cheegerHeat_davies hfinite o h u (hV.min_const (n:ℝ))
    (ae_of_all _ (fun x => min_le_right (V x) (n:ℝ))) ht
  exact H.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (expMulLp_norm_le_weighted hV.continuous.aestronglyMeasurable u hU n) 2)
    (Real.exp_pos _).le)
lemma CurvatureDimension.cheegerHeat_weighted_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ‖(hcd.cheegerHeat_weighted hfinite o h u hV hU ht).1.toLp
        (fun x => cheegerHeat h t u x*Real.exp (V x))‖ ≤
      ‖hU.toLp (fun x => u x*Real.exp (V x))‖*Real.exp ((L:ℝ)^2*t) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_toLp_sq_eq_integral,mul_pow,sq_exp_eq]
  have H := (hcd.cheegerHeat_weighted hfinite o h u hV hU ht).2
  simpa only [mul_assoc] using H

end WeakHessian

end
end InlinedFile0

end OAI

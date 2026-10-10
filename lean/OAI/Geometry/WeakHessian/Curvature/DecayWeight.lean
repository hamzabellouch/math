import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatMassWeighted
import OAI.Geometry.WeakHessian.Geodesics.CdLogMidpointBall
import OAI.Geometry.WeakHessian.LocalBounds.DistDecayCover

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma CurvatureDimension.exists_decay_weight {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) : ∃ a : ℝ, 0 < a ∧ MemLp (fun x => Real.exp (-a*dist x o)) 2 m := by
  let C := N*Real.log 2+8*Real.sqrt (|K|/(N-1))*(N-1)
  refine ⟨|C|+1, by positivity, ?_⟩
  apply memLp_exp_neg_dist_of_growth o ENNReal.toReal_nonneg (by positivity)
    (show C < 2*(|C|+1) by linarith [le_abs_self C,abs_nonneg C])
  exact cd_ball_volume_bound hN hcd hfull hfin o

lemma memLp_exp_dist_of_support (u : Lp ℝ 2 m) {a : ℝ} (ha : 0 ≤ a)
    (o : X) {R : ℝ} (hR : ∀ᵐ x ∂m, R ≤ dist x o → u x = 0) :
    MemLp (fun x => u x*Real.exp (a*dist x o)) 2 m := by
  have H := (Lp.memLp u).const_mul (Real.exp (a*R))
  apply H.mono ((Lp.memLp u).aestronglyMeasurable.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.dist continuous_const))).aestronglyMeasurable)
  filter_upwards [hR] with x hx
  change |u x*Real.exp (a*dist x o)| ≤ |Real.exp (a*R)*u x|
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
  by_cases hs : R ≤ dist x o
  · simp only [hx hs,abs_zero,mul_zero,zero_mul,le_refl]
  · rw [mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_ge hs) ha)) (abs_nonneg _)

omit [MetricSpace X] [BorelSpace X] in
lemma densityMeasure_probability_of_integrable (u : Lp ℝ 2 m)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m) (hmass : ∫ x,u x ∂m = 1) :
    IsProbabilityMeasure (densityMeasure m u) := by
  constructor
  rw [densityMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hu,hmass,ENNReal.ofReal_one]

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma CurvatureDimension.cheegerHeat_mass_supported {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {R : ℝ} (hR : ∀ᵐ x ∂m, R ≤ dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) m ∧ (∫ x,cheegerHeat h t u x ∂m) = ∫ x,u x ∂m := by
  obtain ⟨a,ha,hd⟩ := hcd.exists_decay_weight hN hfull hfin o
  have hV : LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |a*dist x o-a*dist y o| ≤ |a| * dist x y
    rw [← mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)
  have hW := memLp_exp_dist_of_support u ha.le o hR
  have hd' : MemLp (fun x => Real.exp (-(a*dist x o))) 2 m := by
    simpa only [neg_mul] using hd
  refine ⟨integrable_of_memLp_mul_exp (hcd.cheegerHeat_weighted hfin o h u hV hW ht).1 hd', ?_⟩
  exact hcd.cheegerHeat_mass_localized hfin o h u hV hW hd' ht

lemma CurvatureDimension.cheegerHeat_probability_supported {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {R : ℝ} (hR : ∀ᵐ x ∂m, R ≤ dist x o → u x = 0)
    (hu : ∀ᵐ x ∂m, 0 ≤ u x) (hmass : ∫ x,u x ∂m = 1)
    {t : ℝ} (ht : 0 ≤ t) : IsProbabilityMeasure (densityMeasure m (cheegerHeat h t u)) := by
  have H := hcd.cheegerHeat_mass_supported hN hfull hfin o h u hR ht
  exact densityMeasure_probability_of_integrable _ (cheegerHeat_nonneg h ht u hu) H.1 (H.2.trans hmass)
end WeakHessian

end
end InlinedFile0

end OAI

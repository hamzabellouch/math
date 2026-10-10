import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous
import OAI.Geometry.WeakHessian.Sobolev.CompContDiffLipschitz

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
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma regularizedEntropy_integrable {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m) :
    Integrable (fun x => regularizedEntropy a (u x)) m := by
  apply ((Lp.memLp u).integrable_sq.const_mul a⁻¹).mono'
    ((show Continuous (regularizedEntropy a) from continuous_iff_continuousAt.mpr
      (fun y => (regularizedEntropy_hasDeriv ha y).continuousAt)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact ae_of_all _ fun x => by
    have H := lipschitzOn_deriv_quadratic_remainder (convex_univ : Convex ℝ (univ : Set ℝ))
      (fun y _ => regularizedEntropy_hasDeriv ha y) (regularizedLog_lipschitz ha).lipschitzOnWith
      (a := 0) (b := u x) (mem_univ _) (mem_univ _)
    simpa only [regularizedEntropy_zero,regularizedLog_zero,zero_mul,sub_zero,Real.norm_eq_abs,sq_abs,NNReal.coe_mk] using! H

lemma CurvatureDimension.cheegerHeat_regularizedFisher_continuousOn {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => ∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) (Ici 0) := by
  let logLp : Lp ℝ 2 m → Lp ℝ 2 m := (regularizedLog_lipschitz ha).compLp (regularizedLog_zero a)
  have hc : ContinuousOn (fun t => -⟪logLp (cheegerHeat h t u),cheegerHeat h t A⟫_ℝ) (Ici 0) :=
    (((regularizedLog_lipschitz ha).continuous_compLp (regularizedLog_zero a)).comp_continuousOn
      (cheegerHeat_continuousOn hfin h u)).inner (cheegerHeat_continuousOn hfin h A) |>.neg
  apply hc.congr
  intro t ht
  have hL := hcd.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hid := hL.regularizedLog_identity hfin (hcd.global_localGradientParallelogram hfin o h)
    (cheegerHeat_nonneg h ht u hun) ha
  dsimp only
  rw [L2.inner_def]
  have heq : (∫ x,inner (𝕜 := ℝ) (logLp (cheegerHeat h t u) x) (cheegerHeat h t A x) ∂m) =
      ∫ x,cheegerHeat h t A x*regularizedLog a (cheegerHeat h t u x) ∂m := by
    apply integral_congr_ae
    filter_upwards [(regularizedLog_lipschitz ha).coeFn_compLp (regularizedLog_zero a) (cheegerHeat h t u)] with x hx
    simp only [logLp,Function.comp_apply] at hx ⊢
    rw [hx]
    simp only [RCLike.inner_apply,conj_trivial]
  rw [heq,hid,neg_neg]

lemma CurvatureDimension.cheegerHeat_regularizedEntropy_FTC {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ t in 0..b,∫ x,(weakGradient m (cheegerHeat h t u) x)^2/(cheegerHeat h t u x+a) ∂m) =
      (∫ x,regularizedEntropy a (u x) ∂m)-(∫ x,regularizedEntropy a (cheegerHeat h b u x) ∂m) := by
  have hc : Continuous (fun v : Lp ℝ 2 m => ∫ x,regularizedEntropy a (v x) ∂m) :=
    continuous_iff_continuousAt.mpr fun v => (regularizedEntropy_hasFDeriv ha v).continuousAt
  have ht := hc.comp_continuousOn (cheegerHeat_continuousOn hfin h u)
  have hI := (hcd.cheegerHeat_regularizedFisher_continuousOn hfin o h hu hun ha).mono
    (Icc_subset_Ici_self : Icc (0:ℝ) b ⊆ Ici 0)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb (ht.mono Icc_subset_Ici_self)
    (fun t ht => (hcd.cheegerHeat_regularizedEntropy_deriv hfin o h hu hun ha ht.1.le).mono Ioi_subset_Ici_self)
    (hI.intervalIntegrable_of_Icc hb).neg
  rw [intervalIntegral.integral_neg] at H
  simpa only [Function.comp_apply,cheegerHeat_zero,one_apply_eq_self,neg_sub] using (neg_eq_iff_eq_neg.mp H)
end WeakHessian

end
end InlinedFile0

end OAI

import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeat
import OAI.Geometry.WeakHessian.HeatFlow.RealHeatRangeError
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyReal
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogramCheeger
import OAI.Geometry.WeakHessian.Entropy.TruncatedLog

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
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.comp_contDiff_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hLip : LipschitzWith L φ) (hzero : φ 0 = 0) :
    Sobolev m (φ ∘ f) := by
  have hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ (L:ℝ) :=
    ae_of_all _ (fun x => norm_deriv_le_of_lipschitz hLip)
  have hmeas : AEStronglyMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf.1.aemeasurable).abs.aestronglyMeasurable
  apply Sobolev.of_upperGradient hfinite (hLip.comp_memLp hzero hf.1)
    ((weakGradient_isMinimal hf.2.1.2).1.comp_contDiff hf.1.aemeasurable hφ hB)
  simpa only [mul_comm] using memLp_mul_bounded hf.2.2 hmeas (by simpa only [abs_abs] using hB)

lemma IsLaplacian.regularizedLog_identity (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {a : ℝ} (ha : 0 < a) :
    (∫ x, A x * regularizedLog a (u x) ∂m) =
      -(∫ x, (weakGradient m u x)^2 / (u x+a) ∂m) := by
  have hv := hu.1.comp_contDiff_lipschitz hfinite (regularizedLog_contDiff ha)
    (regularizedLog_lipschitz ha) (regularizedLog_zero a)
  have hgamma := gamma_comp_contDiff hfinite hpar hu.1.2.1 hu.1.2.1
    (regularizedLog_contDiff ha) hv.2.1.1 (ae_of_all _ (fun x => regularizedLog_deriv_bound ha (u x)))
  have heq : (∫ x, gamma m u (regularizedLog a ∘ u) x ∂m) =
      (∫ x, (weakGradient m u x)^2/(u x+a) ∂m) := by
    apply integral_congr_ae
    filter_upwards [gamma_comm (m := m) u (regularizedLog a ∘ u), hgamma,
      gamma_self (m := m) u,hun] with x hc hg hs hx
    rw [hc,hg,hs,regularizedLog_deriv ha,max_eq_right (by linarith : a ≤ u x+a)]
    exact inv_mul_eq_div _ _
  have H := hu.2.2 (regularizedLog a ∘ u) hv
  rw [heq] at H
  simp only [Function.comp_apply] at H
  linarith

variable [ProperSpace X]

lemma CurvatureDimension.cheegerHeat_regularizedEntropy_deriv {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m, 0 ≤ u x) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => ∫ x, regularizedEntropy a (cheegerHeat h s u x) ∂m)
      (-(∫ x, (weakGradient m (cheegerHeat h t u) x)^2 / (cheegerHeat h t u x+a) ∂m))
      (Ici t) t := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, hfinite _ Metric.isBounded_ball⟩⟩
  have htime := (cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu ht
  change HasDerivWithinAt (fun s : ℝ => cheegerHeat h s u) (cheegerHeat h t A) (Ici t) t at htime
  have HE := (regularizedEntropy_hasFDeriv ha (cheegerHeat h t u)).comp_hasDerivWithinAt t htime
  have hL := hcd.global_isLaplacian_of_formGenerator hfinite o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hid := hL.regularizedLog_identity hfinite (hcd.global_localGradientParallelogram hfinite o h)
    (cheegerHeat_nonneg h ht u hun) ha
  have hip : (innerSL ℝ ((regularizedLog_memLp ha (cheegerHeat h t u)).toLp
      (fun x => regularizedLog a (cheegerHeat h t u x)))) (cheegerHeat h t A) =
      -(∫ x, (weakGradient m (cheegerHeat h t u) x)^2 / (cheegerHeat h t u x+a) ∂m) := by
    change ⟪((regularizedLog_memLp ha (cheegerHeat h t u)).toLp
      (fun x => regularizedLog a (cheegerHeat h t u x))), (cheegerHeat h t A)⟫_ℝ = _
    rw [L2.inner_def]
    convert hid using 1
    apply integral_congr_ae
    filter_upwards [(regularizedLog_memLp ha (cheegerHeat h t u)).coeFn_toLp] with x hx
    simpa only [RCLike.inner_apply, conj_trivial] using congrArg (fun z : ℝ => cheegerHeat h t A x*z) hx
  simpa only [Function.comp_def,hip] using! HE

end WeakHessian

end
end InlinedFile0

end OAI

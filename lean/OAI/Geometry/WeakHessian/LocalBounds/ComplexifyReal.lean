import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.RealHeat
import OAI.Geometry.WeakHessian.HeatFlow.EulerStepGenerator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
local instance : StarModule ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) where
  star_smul scalar operator := by
    rw [← smul_one_smul ℂ scalar operator, star_smul, star_smul, star_one, smul_one_smul]

@[simp] lemma complexify_ofReal (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (u : Lp ℝ 2 m) :
    complexify m R (ofRealLp m u) = ofRealLp m (R u) := by
  apply complexLp_ext m <;> simp

lemma ofReal_realCfc_pow (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (a : ℝ → ℝ)
    (n : ℕ) (u : Lp ℝ 2 m) :
    ofRealLp m (((realCfc m R a)^n) u) = ((cfc a (complexify m R))^n) (ofRealLp m u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, ofReal_realCfc, ih]

lemma realCfc_eulerStep_eq {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    R (realCfc m R (eulerStep t) u-t⁻¹ • (realCfc m R (eulerStep t) u-u)) =
      realCfc m R (eulerStep t) u := by
  apply ofRealLp_injective m
  rw [← complexify_ofReal m R]
  simp only [map_sub, map_smul, ofReal_realCfc]
  have hinv (v : Lp ℂ 2 m) : (t⁻¹ : ℝ) • v = (t⁻¹ : ℂ) • v := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change Complex.ofReal (t⁻¹) • v = (t⁻¹ : ℂ) • v
    rw [Complex.ofReal_inv]
  simpa only [mul_apply_eq_comp, _root_.sub_apply, hinv, _root_.smul_apply,
    one_apply_eq_self, map_sub] using congrArg (fun T : Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m => T (ofRealLp m u))
    (cfc_eulerStep_eq (complexify_positive m hR) (complexify_le_one m hR1) ht)

lemma realCfc_eulerApproximation_tendsto {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => ((realCfc m R (eulerStep (t/(2:ℝ)^n)))^(2^n:ℕ)) u)
      atTop (𝓝 (realHeat m R t u)) := by
  have H := cfc_eulerApproximation_tendsto (complexify_positive m hR) (complexify_le_one m hR1) ht
  have Ha := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 m) (ofRealLp m u)).continuous.continuousAt.tendsto.comp H
  have Hr := (reLp m).continuous.continuousAt.tendsto.comp Ha
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ← ofReal_realCfc_pow, ← ofReal_realHeat, re_ofRealLp] using Hr

end WeakHessianFunctional

end
end InlinedFile0

end OAI

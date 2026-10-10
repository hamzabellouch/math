import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ReLp
import OAI.Geometry.WeakHessian.HeatFlow.HeatSymbol

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

lemma ofRealLp_norm (f : Lp ℝ 2 m) : ‖ofRealLp m f‖ = ‖f‖ := by
  have h := congrArg Complex.re (ofRealLp_inner m f f)
  have he := inner_self_eq_norm_sq (𝕜 := ℂ) (ofRealLp m f)
  change (⟪ofRealLp m f,ofRealLp m f⟫_ℂ).re = ‖ofRealLp m f‖^2 at he
  rw [he, Complex.ofReal_re, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (ofRealLp m f), norm_nonneg f]

lemma ofRealLp_injective : Function.Injective (ofRealLp m) := by
  intro u v huv
  simpa using congrArg (reLp m) huv

lemma complexify_le_one {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR1 : (1-R).IsPositive) :
    (1-complexify m R).IsPositive := by
  simpa only [complexify_sub, complexify_one] using complexify_positive m hR1

def realHeat (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  realCfc m R (heatSymbol t)

lemma ofReal_realHeat (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ) (u : Lp ℝ 2 m) :
    ofRealLp m (realHeat m R t u) = resolventHeat (complexify m R) t (ofRealLp m u) :=
  ofReal_realCfc m R (heatSymbol t) u

lemma realHeat_zero {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive) :
    realHeat m R 0 = 1 := by
  ext1 u
  apply ofRealLp_injective m
  rw [ofReal_realHeat, resolventHeat_zero (complexify_positive m hR)]
  rfl

lemma realHeat_add (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    realHeat m R (t+s) = realHeat m R t * realHeat m R s := by
  ext1 u
  apply ofRealLp_injective m
  change ofRealLp m (realHeat m R (t+s) u) = ofRealLp m (realHeat m R t (realHeat m R s u))
  simp only [ofReal_realHeat, resolventHeat_add _ ht hs]
  rfl

lemma realHeat_contractive {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (u v : Lp ℝ 2 m) :
    dist (realHeat m R t u) (realHeat m R t v) ≤ dist u v := by
  have H := resolventHeat_contractive (complexify_positive m hR) (complexify_le_one m hR1)
    ht (ofRealLp m u) (ofRealLp m v)
  simpa only [← ofReal_realHeat, dist_eq_norm, ← map_sub, ofRealLp_norm] using H

lemma realHeat_strong_zero {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hi : Function.Injective R) (u : Lp ℝ 2 m) :
    Tendsto (fun t : ℝ => realHeat m R t u) (𝓝[≥] (0:ℝ)) (𝓝 u) := by
  have hc := resolventHeat_strong_zero (complexify_positive m hR) (complexify_le_one m hR1)
    (complexify_range_dense m hR.isSymmetric hi) (ofRealLp m u)
  have hr := (reLp m).continuous.continuousAt.tendsto.comp hc
  simpa only [← ofReal_realHeat, Function.comp_def, re_ofRealLp] using hr

lemma realHeat_symmetric (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m) (t : ℝ) :
    (realHeat m R t).toLinearMap.IsSymmetric := by
  intro u v
  have h := (resolventHeat_positive (complexify m R) t).isSymmetric (ofRealLp m u) (ofRealLp m v)
  change ⟪resolventHeat (complexify m R) t (ofRealLp m u),ofRealLp m v⟫_ℂ =
    ⟪ofRealLp m u,resolventHeat (complexify m R) t (ofRealLp m v)⟫_ℂ at h
  rw [← ofReal_realHeat, ← ofReal_realHeat, ofRealLp_inner, ofRealLp_inner] at h
  exact Complex.ofReal_injective h

end WeakHessianFunctional

end
end InlinedFile0

end OAI

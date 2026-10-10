import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ComplexifyReal
import OAI.Geometry.WeakHessian.HeatFlow.HeatInverseSymbol

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
local instance : Algebra ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) := Algebra.complexToReal
local instance : StarModule ℝ (Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m) where
  star_smul scalar operator := by
    rw [← smul_one_smul ℂ scalar operator, star_smul, star_smul, star_one, smul_one_smul]

lemma realHeat_resolvent {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (t : ℝ) (u : Lp ℝ 2 m) : realHeat m R t (R u) = R (realHeat m R t u) := by
  apply ofRealLp_injective m
  rw [ofReal_realHeat, ← complexify_ofReal m R, ← complexify_ofReal m R, ofReal_realHeat]
  exact resolventHeat_resolvent (complexify_positive m hR) t (ofRealLp m u)

lemma realHeat_mem_range {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) : realHeat m R t u ∈ R.toLinearMap.range := by
  refine ⟨realCfc m R (heatInverseSymbol t) u, ?_⟩
  apply ofRealLp_injective m
  change ofRealLp m (R (realCfc m R (heatInverseSymbol t) u)) = _
  rw [← complexify_ofReal m R, ofReal_realCfc, ofReal_realHeat,
    resolventHeat_eq_resolvent_mul (complexify_positive m hR) ht]
  rfl

lemma realHeat_deriv_range_zero {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m} (hR : R.IsPositive)
    (hR1 : (1-R).IsPositive) (hi : Function.Injective R) (v : Lp ℝ 2 m) :
    HasDerivWithinAt (fun t : ℝ => realHeat m R t (R v)) (R v-v) (Ici 0) 0 := by
  have H := resolventHeat_deriv_range_zero (complexify_positive m hR)
    (complexify_le_one m hR1) (complexify_range_dense m hR.isSymmetric hi) (ofRealLp m v)
  have Hr := (reLp m).hasFDerivAt.comp_hasDerivWithinAt 0 H
  simpa only [Function.comp_def, complexify_ofReal, ← ofReal_realHeat, map_sub,
    re_ofRealLp] using Hr

end WeakHessianFunctional
namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] (m : Measure X)
variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_hasFormGenerator {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    ∃ A, hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u) A := by
  obtain ⟨v,hv⟩ := realHeat_mem_range m hQ.resolvent_positive ht u
  change hQ.resolvent v = realHeat m hQ.resolventLinear t u at hv
  refine ⟨hQ.resolvent v-v, ?_⟩
  rw [← hv]
  exact hQ.isFormGenerator_resolvent v

lemma ClosedQuadraticEnergy.formGenerator_heat {u A : Lp ℝ 2 m}
    (hu : hQ.IsFormGenerator u A) (t : ℝ) :
    hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u)
      (realHeat m hQ.resolventLinear t A) := by
  rw [hQ.isFormGenerator_iff, ← map_sub]
  change hQ.resolventLinear (realHeat m hQ.resolventLinear t (u-A)) = _
  rw [← realHeat_resolvent m hQ.resolvent_positive]
  change realHeat m hQ.resolventLinear t (hQ.resolvent (u-A)) = _
  rw [(hQ.isFormGenerator_iff _ _).mp hu]

def ClosedQuadraticEnergy.heatGeneratorOperator (t : ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  realHeat m hQ.resolventLinear t-realCfc m hQ.resolventLinear (heatInverseSymbol t)

lemma ClosedQuadraticEnergy.heat_generator_explicit {t : ℝ} (ht : 0 < t) (u : Lp ℝ 2 m) :
    hQ.IsFormGenerator (realHeat m hQ.resolventLinear t u) (hQ.heatGeneratorOperator m t u) := by
  rw [hQ.isFormGenerator_iff]
  change hQ.resolvent (realHeat m hQ.resolventLinear t u-
    (realHeat m hQ.resolventLinear t u-realCfc m hQ.resolventLinear (heatInverseSymbol t) u)) = _
  rw [sub_sub_cancel]
  apply ofRealLp_injective m
  change ofRealLp m (hQ.resolventLinear (realCfc m hQ.resolventLinear (heatInverseSymbol t) u)) = _
  rw [← complexify_ofReal m hQ.resolventLinear, ofReal_realCfc, ofReal_realHeat,
    resolventHeat_eq_resolvent_mul (complexify_positive m hQ.resolvent_positive) ht]
  rfl

lemma ClosedQuadraticEnergy.heat_graph_strong_zero
    (hd : hQ.domain.topologicalClosure = ⊤) {u A : Lp ℝ 2 m} (hu : hQ.IsFormGenerator u A) :
    Tendsto (fun t : ℝ => (realHeat m hQ.resolventLinear t u,
      hQ.heatGeneratorOperator m t u)) (𝓝[>] (0:ℝ)) (𝓝 (u,A)) := by
  have h0 := (realHeat_strong_zero m hQ.resolvent_positive hQ.resolvent_le_one
    (hQ.resolvent_injective hd) u).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hA := (realHeat_strong_zero m hQ.resolvent_positive hQ.resolvent_le_one
    (hQ.resolvent_injective hd) A).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have H := h0.prodMk_nhds hA
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  congr 1
  exact hQ.formGenerator_unique hd (hQ.formGenerator_heat m hu t) (hQ.heat_generator_explicit m ht u)

lemma ClosedQuadraticEnergy.heat_deriv_form_zero (hd : hQ.domain.topologicalClosure = ⊤)
    {u A : Lp ℝ 2 m} (hu : hQ.IsFormGenerator u A) :
    HasDerivWithinAt (fun t : ℝ => realHeat m hQ.resolventLinear t u) A (Ici 0) 0 := by
  have H := realHeat_deriv_range_zero m hQ.resolvent_positive hQ.resolvent_le_one
    (hQ.resolvent_injective hd) (u-A)
  change HasDerivWithinAt (fun t : ℝ => realHeat m hQ.resolventLinear t (hQ.resolvent (u-A)))
    (hQ.resolvent (u-A)-(u-A)) (Ici 0) 0 at H
  simpa only [(hQ.isFormGenerator_iff _ _).mp hu, sub_sub_cancel] using H

end WeakHessianFunctional

end
end InlinedFile0

end OAI

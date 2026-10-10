import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatGeneratorOperator

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

lemma realHeat_range_error_apply {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.IsPositive) (hR1 : (1-R).IsPositive) {t : ℝ} (ht : 0 ≤ t) (v : Lp ℝ 2 m) :
    ‖realHeat m R t (R v)-R v‖ ≤ t*‖v‖ := by
  have H := resolventHeat_range_error_apply (complexify_positive m hR)
    (complexify_le_one m hR1) ht (ofRealLp m v)
  simpa only [complexify_ofReal, ← ofReal_realHeat, ← map_sub, ofRealLp_norm] using H

lemma realHeat_range_lipschitz {R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m}
    (hR : R.IsPositive) (hR1 : (1-R).IsPositive) (v : Lp ℝ 2 m) :
    LipschitzOnWith ‖v‖₊ (fun t : ℝ => realHeat m R t (R v)) (Ici 0) := by
  have H (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      dist (realHeat m R t (R v)) (realHeat m R s (R v)) ≤ ‖v‖*|t-s| := by
    have heq : realHeat m R t (R v) = realHeat m R s (realHeat m R (t-s) (R v)) := by
      have he := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T (R v))
        (realHeat_add m R hs (sub_nonneg.mpr hst))
      simpa only [mul_apply_eq_comp, add_sub_cancel] using he
    rw [heq]
    apply (realHeat_contractive m hR hR1 hs _ _).trans
    have H := realHeat_range_error_apply m hR hR1 (sub_nonneg.mpr hst) v
    simpa only [dist_eq_norm, abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using H
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  change dist (realHeat m R t (R v)) (realHeat m R s (R v)) ≤ ‖v‖*|t-s|
  rcases le_total s t with hst | hts
  · exact H s t hs hst
  · have HH := H t s ht hts
    rwa [dist_comm (realHeat m R s (R v)), abs_sub_comm s t] at HH

variable {Q : Lp ℝ 2 m → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.heat_lipschitz_on_generator {u A : Lp ℝ 2 m}
    (hu : hQ.IsFormGenerator u A) :
    LipschitzOnWith ‖u-A‖₊ (fun t : ℝ => realHeat m hQ.resolventLinear t u) (Ici 0) := by
  have H := realHeat_range_lipschitz m hQ.resolvent_positive hQ.resolvent_le_one (u-A)
  change LipschitzOnWith _ (fun t => realHeat m hQ.resolventLinear t (hQ.resolvent (u-A))) _ at H
  simpa only [(hQ.isFormGenerator_iff _ _).mp hu] using H

lemma ClosedQuadraticEnergy.heat_deriv_form_right (hd : hQ.domain.topologicalClosure = ⊤)
    {u A : Lp ℝ 2 m} (hu : hQ.IsFormGenerator u A) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => realHeat m hQ.resolventLinear s u)
      (realHeat m hQ.resolventLinear t A) (Ici t) t := by
  have hg := hQ.heat_deriv_form_zero m hd (hQ.formGenerator_heat m hu t)
  have hc : HasDerivWithinAt (fun s : ℝ => s-t) 1 (Ici t) t :=
    (hasDerivWithinAt_id t (Ici t)).sub_const t
  have H := hg.scomp_of_eq (h := fun s : ℝ => s-t) t hc
    (show MapsTo (fun s : ℝ => s-t) (Ici t) (Ici 0) from
      by intro s hs; exact (show 0 ≤ s-t from sub_nonneg.mpr hs)) (by simp)
  simp only [one_smul, Function.comp_def] at H
  apply H.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have he := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (realHeat_add m hQ.resolventLinear (sub_nonneg.mpr hs) ht)
    simpa only [mul_apply_eq_comp, sub_add_cancel] using he
  · rw [sub_self, realHeat_zero m hQ.resolvent_positive]
    rfl

end WeakHessianFunctional

end
end InlinedFile0

end OAI

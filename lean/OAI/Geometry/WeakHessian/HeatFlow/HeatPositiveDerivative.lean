import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst
import OAI.Geometry.WeakHessian.HeatFlow.HeatClassical

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile131
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_deriv_at_positive (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) {t : ℝ} (ht : 0 < t) :
    ∃ A : Lp ℝ 2 m, (cheeger_closedQuadraticEnergy h).IsFormGenerator (cheegerHeat h t u) A ∧
      HasDerivAt (fun s => cheegerHeat h s u) A t := by
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨B,hB⟩ := Q.heat_hasFormGenerator m (half_pos ht) u
  change Q.IsFormGenerator (cheegerHeat h (t/2) u) B at hB
  let A := cheegerHeat h (t/2) B
  have hg := Q.formGenerator_heat m hB (t/2)
  have he : cheegerHeat h (t/2) (cheegerHeat h (t/2) u) = cheegerHeat h t u := by
    have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
      (cheegerHeat_add h (half_pos ht).le (half_pos ht).le)
    simpa only [add_halves,mul_apply_eq_comp] using H.symm
  change Q.IsFormGenerator (cheegerHeat h (t/2) (cheegerHeat h (t/2) u)) A at hg
  refine ⟨A,he ▸ hg,?_⟩
  have HD := cheegerHeat_deriv_at_generator hfin h hB (half_pos ht)
  have hc := (hasDerivAt_id t).sub_const (t/2)
  have H := HD.scomp_of_eq t hc (by rw [id_eq, sub_half] : t/2 = id t-t/2)
  simp only [Function.comp_def,one_smul,id_eq] at H
  apply H.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show t/2<t by linarith)] with s hs
  have H := congrArg (fun T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m => T u)
    (cheegerHeat_add h (show 0 ≤ s-t/2 by linarith) (half_pos ht).le)
  simpa only [sub_add_cancel,mul_apply_eq_comp] using H
end WeakHessian

end
end InlinedFile131

end OAI

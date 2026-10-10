import OAI.Geometry.Relativity.CKS.SchwarzschildSpacetimeDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCartesianDerivatives

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma lapseSquared_pos_extended {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    0 < lapseSquared m r := by
  by_cases h : 2*m ≤ r
  · exact lapseSquared_pos hm h
  · rw [lapseSquared,velocity_near m r (by linarith)]
    have hp : 0 < r := lt_trans hm hr
    have he : 2*m/r < 2 := (div_lt_iff₀ hp).mpr (by linarith)
    norm_num
    linarith
lemma lapse_smooth_extended {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    ContDiffAt ℝ ∞ (lapse m) r :=
  (lapseSquared_smoothAt (lt_trans hm hr)).sqrt (ne_of_gt (lapseSquared_pos_extended hm hr))
lemma lapse_pos_extended {m r : ℝ} (hm : 0 < m) (hr : m < r) : 0 < lapse m r :=
  Real.sqrt_pos.mpr (lapseSquared_pos_extended hm hr)
lemma lapse_sub_velocity_pos {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    0 < lapse m r - velocity m r := by
  by_cases h : 2*m < r
  · linarith [lapse_dominates_velocity hm h,le_abs_self (velocity m r)]
  · rw [velocity_near m r (by linarith)]
    linarith [lapse_pos_extended hm hr]
lemma advancedSlope_smooth {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    ContDiffAt ℝ ∞ (advancedSlope m) r := by
  apply ((lapse_smooth_extended hm hr).mul
    ((lapse_smooth_extended hm hr).sub (velocity_smooth m).contDiffAt)).inv
  exact ne_of_gt (mul_pos (lapse_pos_extended hm hr) (lapse_sub_velocity_pos hm hr))
lemma advancedTime_hasDerivAt {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    HasDerivAt (advancedTime m) (advancedSlope m r) r := by
  have hs : ContinuousOn (advancedSlope m) (Ioi m) := fun s hs =>
    (advancedSlope_smooth hm hs).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (advancedSlope m) volume (2*m) r := by
    apply (hs.mono ?_).intervalIntegrable
    intro s h
    have hh : min (2*m) r ≤ s := h.1
    have hmin : m < min (2*m) r := lt_min (by linarith) hr
    exact lt_of_lt_of_le hmin hh
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hs.stronglyMeasurableAtFilter isOpen_Ioi r hr) (advancedSlope_smooth hm hr).continuousAt
lemma advancedTime_smooth {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (advancedTime m) (Ioi m) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  refine ⟨fun r hr => (advancedTime_hasDerivAt hm hr).differentiableAt.differentiableWithinAt,?_⟩
  apply ContDiffOn.congr (f := advancedSlope m)
    (fun r hr => (advancedSlope_smooth hm hr).contDiffWithinAt)
  intro r hr
  exact (advancedTime_hasDerivAt hm hr).deriv
lemma advancedGraph_smooth {m : ℝ} (hm : 0 < m) {x : E3} (hr : m < ‖x‖) :
    ContDiffAt ℝ ∞ (advancedGraph m) x := by
  have hx := norm_pos_iff.mp (lt_trans hm hr)
  exact (((advancedTime_smooth hm).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x
    (contDiffAt_norm ℝ hx)).prodMk contDiffAt_id
lemma advancedGraph_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : m < ‖x‖) (a : E3) :
    fderiv ℝ (advancedGraph m) x a = graphTangent m x a := by
  have hx := norm_pos_iff.mp (lt_trans hm hr)
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := ((advancedTime_hasDerivAt hm hr).hasFDerivAt.comp x hn.hasFDerivAt).prodMk (hasFDerivAt_id x)
  rw [show fderiv ℝ (advancedGraph m) x = _ from h.fderiv]
  simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
    norm_derivative hx,graphTangent]
  congr 1
  ring
end CKSSchwarzschild

end

end OAI

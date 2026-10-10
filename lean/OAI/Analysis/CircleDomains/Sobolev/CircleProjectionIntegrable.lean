import OAI.Analysis.CircleDomains.Topology.CircleProjectionEndpoints
import OAI.Analysis.CircleDomains.Sobolev.BoundedIntervalIntegral
import OAI.Analysis.CircleDomains.Rigidity.MatchedInnerCircleFlux

namespace OAI

/-! The actual circle endpoint values are measurable and bounded, hence
all axial and quarter-arc flux integrals are genuine integrals. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem horizontalCirclePoint_mem (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (c.im-r) (c.im+r)) (s : Bool) : horizontalCirclePoint s c r y ∈ closedBall c r := by
  cases s
  · have h := (mem_closedBall_iff_mem_horizontalChord c hr hy).mpr
      (left_mem_Icc.mpr (horizontalChord_valid c r y))
    simpa [horizontalCirclePoint,horizontalChord,quadrantSign,sub_eq_add_neg] using h
  · have h := (mem_closedBall_iff_mem_horizontalChord c hr hy).mpr
      (right_mem_Icc.mpr (horizontalChord_valid c r y))
    simpa [horizontalCirclePoint,horizontalChord,quadrantSign,sub_eq_add_neg] using h

 theorem verticalCirclePoint_mem (c : ℂ) {r x : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ Icc (c.re-r) (c.re+r)) (t : Bool) : verticalCirclePoint t c r x ∈ closedBall c r := by
  have hhy : x ∈ Icc (transverseCoordinate 1 c-r) (transverseCoordinate 1 c+r) := hx
  have hvalid : (axialChord 1 c r x).1 ≤ (axialChord 1 c r x).2 := horizontalChord_valid _ _ _
  cases t
  · have h := (mem_closedBall_iff_mem_axialChord 1 c hr hhy).mpr (left_mem_Icc.mpr hvalid)
    simpa [verticalCirclePoint,axialChord,horizontalChord,axialSwap,quadrantSign,
      complexCoordinateLine,realCoordinateLine,Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg] using h
  · have h := (mem_closedBall_iff_mem_axialChord 1 c hr hhy).mpr (right_mem_Icc.mpr hvalid)
    simpa [verticalCirclePoint,axialChord,horizontalChord,axialSwap,quadrantSign,
      complexCoordinateLine,realCoordinateLine,Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I,sub_eq_add_neg] using h

 theorem continuous_horizontalCirclePoint (s : Bool) (c : ℂ) (r : ℝ) :
    Continuous (horizontalCirclePoint s c r) := by
  change Continuous (fun y => Complex.equivRealProdCLM.symm
    (c.re+quadrantSign s*Real.sqrt (r^2-(y-c.im)^2),y))
  fun_prop

 theorem continuous_verticalCirclePoint (t : Bool) (c : ℂ) (r : ℝ) :
    Continuous (verticalCirclePoint t c r) := by
  change Continuous (fun x => Complex.equivRealProdCLM.symm
    (x,c.im+quadrantSign t*Real.sqrt (r^2-(x-c.re)^2)))
  fun_prop

 theorem circle_projection_integrable {F : ℂ → ℂ} (hF : Measurable F) (c : ℂ) {r B : ℝ}
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hb : ∀ z ∈ closedBall c r, ‖F z‖ ≤ B) :
    IntervalIntegrable (fun y => (F (horizontalCirclePoint true c r y)).re-
      (F (horizontalCirclePoint false c r y)).re) volume (c.im-r) (c.im+r) ∧
    IntervalIntegrable (fun x => (F (verticalCirclePoint true c r x)).im-
      (F (verticalCirclePoint false c r x)).im) volume (c.re-r) (c.re+r) := by
  constructor
  · apply intervalIntegrable_of_measurable_bound (C := 2*B)
      ((Complex.measurable_re.comp (hF.comp (continuous_horizontalCirclePoint true c r).measurable)).sub
        (Complex.measurable_re.comp (hF.comp (continuous_horizontalCirclePoint false c r).measurable)))
      (mul_nonneg (by norm_num) hB)
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have hright := (Complex.abs_re_le_norm _).trans (hb _ (horizontalCirclePoint_mem c hr hy true))
    have hleft := (Complex.abs_re_le_norm _).trans (hb _ (horizontalCirclePoint_mem c hr hy false))
    exact (abs_sub _ _).trans (by dsimp only [Function.comp_apply]; linarith)
  · apply intervalIntegrable_of_measurable_bound (C := 2*B)
      ((Complex.measurable_im.comp (hF.comp (continuous_verticalCirclePoint true c r).measurable)).sub
        (Complex.measurable_im.comp (hF.comp (continuous_verticalCirclePoint false c r).measurable)))
      (mul_nonneg (by norm_num) hB)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have htop := (Complex.abs_im_le_norm _).trans (hb _ (verticalCirclePoint_mem c hr hx true))
    have hbottom := (Complex.abs_im_le_norm _).trans (hb _ (verticalCirclePoint_mem c hr hx false))
    exact (abs_sub _ _).trans (by dsimp only [Function.comp_apply]; linarith)

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Modulus.CircleWedgeCost
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! The intrinsic circle differential is Borel measurable for a Borel
circle coordinate. Two fixed cuts suffice on the continuity set; at a
discontinuity every real branch is nondifferentiable and its derivative
is zero. This supplies the actual gradient used in grid averaging. -/

open Set Function Filter MeasureTheory Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem circleFDeriv_eq_fixed_cut
    {f : (ℝ × ℝ) → UnitAddCircle} {x : ℝ × ℝ} (hf : ContinuousAt f x)
    {a : ℝ} (ha : f x ≠ (a : UnitAddCircle)) :
    circleFDeriv f x = fderiv ℝ (circleBranch f a) x := by
  apply fderiv_lifts_eq
    (continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco _ _ (circleCut_ne f x)).comp hf))
    (continuous_subtype_val.continuousAt.comp
      ((AddCircle.continuousAt_equivIco _ _ ha).comp hf))
  exact Eventually.of_forall fun y => (coe_circleBranch f _ y).trans (coe_circleBranch f _ y).symm

 theorem circleFDeriv_eq_zero_of_not_continuousAt
    {f : (ℝ × ℝ) → UnitAddCircle} {x : ℝ × ℝ} (hf : ¬ContinuousAt f x) :
    circleFDeriv f x = 0 := by
  apply fderiv_zero_of_not_differentiableAt
  intro hd
  apply hf
  have hc := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp hd.continuousAt
  exact hc.congr (Eventually.of_forall (coe_circleBranch f _))

 theorem measurable_circleFDeriv {f : (ℝ × ℝ) → UnitAddCircle} (hf : Measurable f) :
    Measurable (circleFDeriv f) := by
  let C : Set (ℝ × ℝ) := {x | ContinuousAt f x}
  let A : Set (ℝ × ℝ) := {x | f x ≠ (0 : UnitAddCircle)}
  have hC : MeasurableSet C := measurableSet_of_continuousAt f
  have hA : MeasurableSet A := hf (isClosed_singleton.measurableSet.compl)
  have hhalf : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro he
    have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have hh : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 hh).mp he
    norm_num at heq
  have heq : circleFDeriv f = C.piecewise
      (A.piecewise (fderiv ℝ (circleBranch f 0)) (fderiv ℝ (circleBranch f (1 / 2))))
      (fun _ => 0) := by
    funext x
    by_cases hc : x ∈ C
    · rw [piecewise_eq_of_mem C _ _ hc]
      by_cases ha : x ∈ A
      · rw [piecewise_eq_of_mem A _ _ ha]
        exact circleFDeriv_eq_fixed_cut hc ha
      · rw [piecewise_eq_of_notMem A _ _ ha]
        apply circleFDeriv_eq_fixed_cut hc
        simpa only [A, mem_ofPred_eq, not_not.mp ha] using hhalf
    · rw [piecewise_eq_of_notMem C _ _ hc]
      exact circleFDeriv_eq_zero_of_not_continuousAt hc
  rw [heq]
  exact ((measurable_fderiv ℝ _).piecewise hA (measurable_fderiv ℝ _)).piecewise hC measurable_const

 theorem measurable_circleGradient {f : (ℝ × ℝ) → UnitAddCircle} (hf : Measurable f) :
    Measurable (circleGradient f) :=
  (((ContinuousLinearMap.measurable_apply (1, 0)).comp (measurable_circleFDeriv hf)).prodMk
    ((ContinuousLinearMap.measurable_apply (0, 1)).comp (measurable_circleFDeriv hf)))

end CircleDomainRigidity.FiniteTransfer

end

end OAI

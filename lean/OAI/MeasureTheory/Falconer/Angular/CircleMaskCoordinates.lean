import OAI.MeasureTheory.Falconer.Angular.ActualAngleMasks
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Algebra.Ring.Periodic

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

noncomputable def sourceAngle (dir : UnitCircle) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm (dir:Plane))

@[fun_prop] theorem measurable_sourceAngle : Measurable sourceAngle := by
  unfold sourceAngle
  exact Complex.measurable_arg.comp
    (Complex.orthonormalBasisOneI.repr.symm.continuous.measurable.comp continuous_subtype_val.measurable)

theorem sourceUnitDirection_sourceAngle (dir : UnitCircle) :
    sourceUnitDirection (sourceAngle dir) = dir := by
  apply Subtype.ext
  let z := Complex.orthonormalBasisOneI.repr.symm (dir:Plane)
  have hn : ‖z‖ = 1 := (Complex.orthonormalBasisOneI.repr.symm.norm_map _).trans dir.property
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [hn,one_mul] at hc hs
  change Complex.orthonormalBasisOneI.repr
    ((Real.cos (Complex.arg z):ℂ)+(Real.sin (Complex.arg z):ℂ)*Complex.I) = _
  rw [hc,hs,Complex.re_add_im]
  exact Complex.orthonormalBasisOneI.repr.apply_symm_apply _

theorem sourceAngle_sourceUnitDirection (θ : ℝ) :
    sourceAngle (sourceUnitDirection θ) =
      Complex.arg ((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I) := by
  simp only [sourceAngle,sourceUnitDirection,sourceDirection,LinearIsometryEquiv.symm_apply_apply]

theorem sourceTestMask_periodic (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.Periodic (sourceTestMask G d hd) (2*Real.pi) := by
  apply smoothAngleMask_periodic
  intro θ
  have he : sourceUnitDirection (θ+2*Real.pi) = sourceUnitDirection θ := by
    apply Subtype.ext
    simp only [sourceUnitDirection,sourceDirection,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [mem_preimage,he]

noncomputable def circleTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) : UnitCircle → ℝ :=
  fun dir => sourceTestMask G d hd (sourceAngle dir)

@[fun_prop] theorem measurable_circleTestMask (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Measurable (circleTestMask G d hd) :=
  (sourceTestMask_contDiff G d hd).continuous.measurable.comp measurable_sourceAngle

theorem circleTestMask_bounds (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (dir : UnitCircle) :
    0 ≤ circleTestMask G d hd dir ∧ circleTestMask G d hd dir ≤ 1 := sourceTestMask_bounds _ _ _ _

theorem circleTestMask_eq_one (G : Set UnitCircle) (d : ℝ) (hd : 0 < d)
    {dir : UnitCircle} (hdir : dir ∈ G) : circleTestMask G d hd dir = 1 := by
  apply sourceTestMask_eq_one
  simpa only [sourceUnitDirection_sourceAngle] using hdir

theorem circleTestMask_comp (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    circleTestMask G d hd (sourceUnitDirection θ) = sourceTestMask G d hd θ := by
  unfold circleTestMask
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := (sourceTestMask_periodic G d hd).int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

theorem circleTestMask_angular_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (fun θ => circleTestMask G d hd (sourceUnitDirection θ)) := by
  simpa only [circleTestMask_comp] using sourceTestMask_contDiff G d hd

theorem circleTestMask_failure_le (G : Set UnitCircle) (hG : MeasurableSet G)
    (d : ℝ) (hd : 0 < d) :
    sourceArcLength {dir | circleTestMask G d hd dir ≠ 1} ≤ sourceArcLength Gᶜ := by
  rw [measure_eq_iInf {dir | circleTestMask G d hd dir ≠ 1}]
  refine iInf_le_of_le Gᶜ (iInf_le_of_le ?_ (iInf_le_of_le hG.compl le_rfl))
  intro dir hdir hmem
  exact hdir (circleTestMask_eq_one G d hd hmem)

end PlanarFalconer

end OAI

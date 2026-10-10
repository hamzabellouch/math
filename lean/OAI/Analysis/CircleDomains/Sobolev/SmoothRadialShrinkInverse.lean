import OAI.Analysis.CircleDomains.Sobolev.SmoothRadialShrink
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! The radial contraction has an everywhere invertible differential,
so its actual global inverse is smooth. -/
open Set Function Filter Metric
open scoped Topology ContDiff RealInnerProductSpace
noncomputable section
namespace CircleDomainRigidity

lemma radialShrink_fderiv_injective {t a b : ℝ} (ht : 0<t) (ht1 : t≤1)
    (ha : 0<a) (hab : a<b) (z : ℂ) :
    Injective (fderiv ℝ (radialShrink t a b) z) := by
  let q : ℝ → ℝ := fun s => t+(1-t)*Real.smoothTransition ((s-a^2)/(b^2-a^2))
  have hden : 0<b^2-a^2 := by nlinarith
  have hq : ContDiff ℝ ∞ q := by dsimp [q];fun_prop
  have hmono : Monotone q := by
    intro r s hrs
    dsimp [q]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hrs _) hden.le)
  have hqp : 0<q (‖z‖^2) := radialShrinkFactor_pos ht ht1
  have hdq : 0≤deriv q (‖z‖^2) := hmono.deriv_nonneg
  have hcomp := (hq.differentiable (by simp) (‖z‖^2)).hasDerivAt.comp_hasFDerivAt z
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hf := hcomp.smul (hasFDerivAt_id z)
  have heq : (fun x : ℂ => q (‖x‖^2) • x)=radialShrink t a b := rfl
  change HasFDerivAt (fun x : ℂ => q (‖x‖^2) • x) _ z at hf
  rw [heq] at hf
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hf.fderiv] at hv
  have he : q (‖z‖^2) • v + (deriv q (‖z‖^2) * (2*(inner ℝ z v))) • z=0 := by
    simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,comp_apply,id_eq] at hv
    have hscalar : deriv q (‖z‖^2) • (2 • (inner ℝ z v)) =
        deriv q (‖z‖^2) * (2 * (inner ℝ z v)) := by
      simp only [two_smul,smul_eq_mul]
      ring
    rwa [hscalar] at hv

  have hi := congrArg (fun w : ℂ => (inner ℝ v w)) he
  have hvv : (inner ℝ v v)=‖v‖^2 := real_inner_self_eq_norm_sq v
  have hzv : (inner ℝ v z)=(inner ℝ z v) := (real_inner_comm v z).symm
  simp only [inner_add_right,inner_smul_right,inner_zero_right,hvv,hzv] at hi
  have hsum : q (‖z‖^2)*‖v‖^2 + 2*deriv q (‖z‖^2)*(inner ℝ z v)^2=0 := by
    linear_combination hi
  have hnon : 0≤2*deriv q (‖z‖^2)*(inner ℝ z v)^2 :=
    mul_nonneg (mul_nonneg (by norm_num) hdq) (sq_nonneg _)
  have hz : q (‖z‖^2)*‖v‖^2=0 :=
    le_antisymm (by linarith) (mul_nonneg hqp.le (sq_nonneg _))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hqp.ne'))

lemma smoothRadialShrinkHomeomorph_inverse_contDiff {t a b : ℝ}
    (ht : 0<t) (ht1 : t≤1) (ha : 0<a) (hab : a<b) :
    ContDiff ℝ ∞ ((smoothRadialShrinkHomeomorph ht ht1 ha hab).symm : ℂ → ℂ) := by
  let H := smoothRadialShrinkHomeomorph ht ht1 ha hab
  let A (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ (radialShrink t a b) z).toLinearMap
      ⟨radialShrink_fderiv_injective ht ht1 ha hab z,
        (LinearMap.injective_iff_surjective).mp (radialShrink_fderiv_injective ht ht1 ha hab z)⟩).toContinuousLinearEquiv
  have hd (z : ℂ) : HasFDerivAt (H : ℂ → ℂ) (A z : ℂ →L[ℝ] ℂ) z :=
    ((radialShrink_contDiff t a b).differentiable (by simp) z).hasFDerivAt
  exact H.contDiff_symm hd (radialShrink_contDiff t a b)

end CircleDomainRigidity

end

end OAI

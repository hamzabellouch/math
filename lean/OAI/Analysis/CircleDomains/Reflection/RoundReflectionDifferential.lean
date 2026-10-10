import OAI.Analysis.CircleDomains.Reflection.SmoothReflectionConjugacy
import OAI.Analysis.CircleDomains.Topology.SphereCoefficient

namespace OAI

/-! Plane formula and differential of a circular reflection off its pole. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

def roundReflectionPlane (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  c+(r:ℂ)^2/(star (z-c))

lemma roundReflectionPlane_ne_center (c : ℂ) {r : ℝ} (hr : r≠0) {z : ℂ} (hz : z≠c) :
    roundReflectionPlane c r z≠c := by
  have hr' : (r:ℂ)≠0 := by exact_mod_cast hr
  intro hh
  have hh' : (r:ℂ)^2/star (z-c)=0 := by
    exact add_left_cancel (hh.trans (add_zero c).symm)
  exact (div_ne_zero (pow_ne_zero 2 hr') (star_ne_zero.mpr (sub_ne_zero.mpr hz))) hh'

lemma roundReflectionPlane_involutive (c : ℂ) {r : ℝ} (hr : r≠0) :
    Involutive (roundReflectionPlane c r) := by
  intro z
  by_cases hz : z=c
  · simp [roundReflectionPlane,hz]
  · have hr' : (r:ℂ)≠0 := by exact_mod_cast hr
    simp only [roundReflectionPlane,add_sub_cancel_left,map_div₀,map_pow,
      Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
    field_simp [sub_ne_zero.mpr hz,hr']
    ring

lemma roundReflectionPlane_differentiable {c z : ℂ} {r : ℝ} (hz : z≠c) :
    DifferentiableAt ℝ (roundReflectionPlane c r) z := by
  unfold roundReflectionPlane
  apply DifferentiableAt.const_add
  convert ((Complex.conjCLE.differentiableAt.comp z (differentiableAt_id.sub_const c)).inv
      (star_ne_zero.mpr (sub_ne_zero.mpr hz))).const_mul ((r:ℂ)^2) using 1
  rfl

lemma partialZ_eq_deriv_of_complex {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    partialZ f z=deriv f z := by
  have hh := fderiv_wirtinger f z 1
  rw [partialBar_zero_of_differentiableAt hf,mul_one,zero_mul,add_zero] at hh
  rw [hf.fderiv_restrictScalars ℝ] at hh
  exact hh.symm

lemma roundReflectionPlane_partials {c z : ℂ} {r : ℝ} (hz : z≠c) :
    partialZ (roundReflectionPlane c r) z=0 ∧
      partialBar (roundReflectionPlane c r) z= -(r:ℂ)^2/(star (z-c))^2 := by
  let f : ℂ → ℂ := fun w => star c+(r:ℂ)^2/(w-c)
  have hd : HasDerivAt f (-(r:ℂ)^2/(z-c)^2) z := by
    convert (((hasDerivAt_id z).sub_const c).inv (sub_ne_zero.mpr hz)).const_mul ((r:ℂ)^2)
      |>.const_add (star c) using 1
    · funext w; dsimp [f]; ring
    · dsimp; ring
  have he : roundReflectionPlane c r=fun w => star (f w) := by
    funext w
    simp [roundReflectionPlane,f]
  rw [he]
  have hh := partials_conjugate (hd.differentiableAt.restrictScalars ℝ)
  rw [partialBar_zero_of_differentiableAt hd.differentiableAt,
    partialZ_eq_deriv_of_complex hd.differentiableAt,hd.deriv] at hh
  simpa only [star_zero,map_neg,map_div₀,map_pow,Complex.star_def,Complex.conj_ofReal] using hh

lemma roundReflectionPlane_phase {c z : ℂ} {r : ℝ} (hz : z≠c) :
    partialBar (roundReflectionPlane c r) z=
      circleReflectionPhase c z*star (partialBar (roundReflectionPlane c r) z) := by
  rw [(roundReflectionPlane_partials hz).2]
  simp only [circleReflectionPhase,ite_eq_right hz,map_neg,map_div₀,map_pow,
    Complex.star_def,Complex.conj_ofReal,Complex.conj_conj]
  field_simp [sub_ne_zero.mpr hz]

end CircleDomainRigidity

end

end OAI

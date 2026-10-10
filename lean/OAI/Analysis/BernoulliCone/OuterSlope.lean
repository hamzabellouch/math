import OAI.Analysis.BernoulliCone.SeamCalibration

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma Zsigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
  have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by
    simpa only [inner_axis,angle] using (show angle x∈Ioo (-1:ℝ) 1 from abs_lt.mp ha)
  rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
  simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
lemma outerSigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient outerSigned x=polarGradient axis x (f (angle x)) (fp (angle x))+
      (capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x)) := by
  have hdz: DifferentiableAt ℝ Zsigned x := (signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk: DifferentiableAt ℝ KSup x := (KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  change gradient (fun x=>Zsigned x+capAmplitude*KSup x) x=_
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,
    Zsigned_gradient hx ha,KSup_gradient hx ha,smul_smul]
lemma outer_zero_coefficient {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)= -f (angle x)/gSup (angle x) := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hn:‖x‖≠0:=norm_ne_zero_iff.mpr hx
  have hg:(gSup (angle x))≠0:=(gSup_pos ha).ne'
  rw [outerSigned,Zsigned_eq,KSup,lift,inner_axis] at hz
  change ‖x‖*f (angle x)+capAmplitude*(‖x‖^(-2:ℝ)*gSup (angle x))=0 at hz
  field_simp
  linarith
lemma GSup_even (t:ℝ) : GSup (-t)=GSup t := by
  simp only [GSup,f_neg,fp_neg_arg,qSup,neg_sq]
  ring
lemma GSup_abs (t:ℝ) : GSup |t|=GSup t := by
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,GSup_even]
lemma outer_zero_slope {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    ‖gradient outerSigned x‖^2=GSup (angle x) := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hg:(gSup (angle x))≠0:=(gSup_pos ha).ne'
  have he:gradient outerSigned x=polarGradient axis x (3*f (angle x))
      (fp (angle x)-f (angle x)*qSup (angle x)) := by
    rw [outerSigned_gradient hx ha,outer_zero_coefficient hq hz,qSup_eq ha]
    apply ext_inner_right ℝ
    intro v
    simp only [polarGradient,inner_add_left,inner_sub_left,real_inner_smul_left]
    field_simp
    ring
  rw [he,norm_sq_polarGradient axis_norm hx]
  simp only [inner_axis,GSup,angle]
  ring
lemma outer_zero_angle {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    t7 < |angle x| ∧ |angle x|≤3/5 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  refine ⟨?_,outer_nonnegative_angle hq (le_of_eq hz.symm)⟩
  have hk:=mul_pos capAmplitude_pos (KSup_pos hx ha)
  have hf:f (angle x)<0 := by
    rw [outerSigned,Zsigned_eq] at hz
    have hr:0<‖x‖:=norm_pos_iff.mpr hx
    nlinarith
  by_contra hh
  have he:p (angle x)=f (angle x):=p_eq_f (not_lt.mp hh)
  have hp:=p_nonneg (angle x)
  rw [he] at hp
  linarith
/-- Strict free-boundary slope for the actual exterior function, not just its
one-variable numerical certificate. -/
theorem outer_zero_slope_lt {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hz:outerSigned x=0) :
    ‖gradient outerSigned x‖^2<c7 := by
  rw [outer_zero_slope (by linarith) hz,←GSup_abs]
  exact GSup_lt_c7 (outer_zero_angle hq hz).1 (outer_zero_angle hq hz).2
end Bernoulli.DeSilvaJerison

end
end

end OAI

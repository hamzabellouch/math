import OAI.Analysis.BernoulliCone.FluxBounds

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma upperFamily_outer_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2<Cylindrical.radiusSq axis x) (hp:0<upperFamily l x) :
    gradient (upperFamily l) x=κ • gradient Zsigned x+
      (κ*capAmplitude*l^3) • gradient KSup x := by
  have hqp:0<Cylindrical.radiusSq axis x:=(sq_pos_of_pos hl).trans hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hdZ:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdK:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have he:upperFamily l =ᶠ[𝓝 x] (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) := by
    filter_upwards [((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt).eventually (lt_mem_nhds hq),
      (upperFamily_continuous l).continuousAt.eventually (lt_mem_nhds hp)] with y hy hpy
    rw [upperFamily_outer_formula hl hy.le] at hpy ⊢
    have hh:0<Zsigned y+capAmplitude*l^3*KSup y:=by
      have hm:=pos_of_mul_pos_right hpy κ_pos.le
      simpa using hm
    rw [max_eq_left hh.le]
  rw [gradient,he.fderiv_eq]
  change gradient (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) x=_
  have hdf:DifferentiableAt ℝ (fun y=>Zsigned y+capAmplitude*l^3*KSup y) x:=
    hdZ.add (hdK.const_mul (capAmplitude*l^3))
  rw [gradient_const_mul κ hdf,
    gradient_add' hdZ (hdK.const_mul (capAmplitude*l^3)),gradient_const_mul (capAmplitude*l^3) hdK,smul_add,smul_smul]
  congr 2
  ring

/-- On the actual exterior branch the inverse leaf parameter cancels completely.
The calibration extends affinely to the lower graph; there is no cube-root
singularity in the field itself. -/
theorem upperCalibration_outer_affine {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:(upperParameter p.1 p.2)^2<Cylindrical.radiusSq axis p.1) :
    upperCalibration p=κ • gradient Zsigned p.1+
      ((p.2-κ*Zsigned p.1)/KSup p.1) • gradient KSup p.1 := by
  let l:=upperParameter p.1 p.2
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  change 0<l at hl
  change upperFamily l p.1=p.2 at he
  have ht:0<p.2:=(U_nonneg _).trans_lt hp
  have hpos:0<upperFamily l p.1:=by rw [he]; exact ht
  have hqp:0<Cylindrical.radiusSq axis p.1:=(sq_pos_of_pos hl).trans hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hK:KSup p.1≠0:=(KSup_pos hx ha).ne'
  have hqe:Cylindrical.radiusSq axis (l⁻¹ • p.1)≠1:=by
    rw [Cylindrical.radiusSq_smul]
    have hh:(l⁻¹)^2*Cylindrical.radiusSq axis p.1>1:=by
      rw [inv_pow,←div_eq_inv_mul]
      change 1<Cylindrical.radiusSq axis p.1/l^2
      exact (lt_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [one_mul] using hq)
    exact ne_of_gt hh
  rw [upperCalibration,Foliation.spatialGradient_eq
    ((upperFamily_contDiffAt_swap hl hpos hqe).differentiableAt (by simp)),
    upperFamily_outer_gradient hl hq hpos]
  congr 1
  have hh:=upperFamily_outer_formula hl hq.le
  rw [he] at hh
  have hsg:0<Zsigned p.1+capAmplitude*l^3*KSup p.1:=by
    have hm:0 < max (Zsigned p.1+capAmplitude*l^3*KSup p.1) 0:=by
      exact pos_of_mul_pos_right (hh ▸ ht) κ_pos.le
    simpa using hm
  rw [max_eq_left hsg.le] at hh
  apply congrArg (fun a:ℝ=>a • gradient KSup p.1)
  apply (eq_div_iff hK).mpr
  nlinarith [hh]
end Bernoulli.DeSilvaJerison

end
end

end OAI

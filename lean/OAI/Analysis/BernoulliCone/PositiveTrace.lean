import OAI.Analysis.BernoulliCone.PrimitiveBound

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma U_lt_upperFamily {x:Space 7} (hx:0<U x) {l:ℝ} (hl:0<l) :
    U x<upperFamily l x := by
  have ha:0<l/2:=half_pos hl
  have hs:=U_le_upperFamily x ha
  exact hs.trans_lt (upperFamily_strict ha (by linarith) (hx.trans_le hs))
lemma U_pos_radiusSq {x:Space 7} (hx:0<U x) : 0<Cylindrical.radiusSq axis x := by
  have hq:=Cylindrical.radiusSq_nonneg axis x axis_norm
  by_contra hn
  have he:Cylindrical.radiusSq axis x=0:=le_antisymm (not_lt.mp hn) hq
  rw [U_zero_of_radiusSq_zero he] at hx
  exact lt_irrefl _ hx
lemma upperParameter_eventually_outer {x:Space 7} (hx:0<U x) :
    ∀ᶠ t:ℝ in 𝓝[>] (U x),(upperParameter x t)^2<Cylindrical.radiusSq axis x := by
  have hq:=U_pos_radiusSq hx
  let l:=Real.sqrt (Cylindrical.radiusSq axis x)
  have hl:0<l:=Real.sqrt_pos.mpr hq
  have hlt:=U_lt_upperFamily hx hl
  have hn:∀ᶠ t:ℝ in 𝓝[>] (U x),t<upperFamily l x :=
    (gt_mem_nhds hlt).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with t ht htx
  have hh:upperParameter x t<l:=(upperParameter_lt_iff htx hl).mpr ht
  have hp:= (upperParameter_spec htx).1
  have hsq: (upperParameter x t)^2<l^2 := (sq_lt_sq₀ hp.le hl.le).mpr hh
  simpa only [l,Real.sq_sqrt hq.le] using hsq
lemma U_eq_signed_of_pos {x:Space 7} (hx:0<U x) : U x=κ*Zsigned x := by
  have hq := U_pos_radiusSq hx
  rw [U_eq_signed_pospart hq] at hx ⊢
  have hh:0<Zsigned x:=by
    have hh1:0 < max (Zsigned x) 0:=pos_of_mul_pos_right hx κ_pos.le
    simpa using hh1
  rw [max_eq_left hh.le]
lemma gradient_U_eq_signed {x:Space 7} (hx:0<U x) :
    gradient U x=κ • gradient Zsigned x := by
  have hn:∀ᶠ y in 𝓝 x,0<U y:=U_continuous.continuousAt.eventually (lt_mem_nhds hx)
  have he:U =ᶠ[𝓝 x] (fun y=>κ*Zsigned y):=hn.mono fun y hy=>U_eq_signed_of_pos hy
  obtain ⟨hx0,ha⟩:=radiusSq_pos_data (U_pos_radiusSq hx)
  rw [gradient,he.fderiv_eq]
  exact gradient_const_mul κ ((signed_contDiffAt (n:=1) hx0 ha).differentiableAt (by norm_num))
lemma normalized_radiusSq_ne_one {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2<Cylindrical.radiusSq axis x) :
    Cylindrical.radiusSq axis (l⁻¹ • x)≠1 := by
  rw [Cylindrical.radiusSq_smul]
  have hh:(l⁻¹)^2*Cylindrical.radiusSq axis x>1:=by
    rw [inv_pow,←div_eq_inv_mul]
    change 1<Cylindrical.radiusSq axis x/l^2
    exact (lt_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [one_mul] using hq)
  exact ne_of_gt hh
lemma upperFlux_outer_affine {x:Space 7} {t:ℝ} (ht:U x<t)
    (hq:(upperParameter x t)^2<Cylindrical.radiusSq axis x) :
    upperFlux (x,t)=κ • gradient Zsigned x+((t-κ*Zsigned x)/KSup x) • gradient KSup x := by
  have hl:0<upperParameter x t:=(upperParameter_spec ht).1
  have hqe:=normalized_radiusSq_ne_one hl hq
  rw [upperFlux_eq_calibration (p:=(x,t)) ht hqe]
  exact upperCalibration_outer_affine (p:=(x,t)) ht hq
/-- The actual bounded field has the exact positive-phase lower trace. -/
theorem upperFlux_tendsto_positive_trace {x:Space 7} (hx:0<U x) :
    Tendsto (fun t:ℝ=>upperFlux (x,t)) (𝓝[>] (U x)) (𝓝 (gradient U x)) := by
  have he:(fun t:ℝ=>upperFlux (x,t)) =ᶠ[𝓝[>] (U x)]
      (fun t=>κ • gradient Zsigned x+((t-κ*Zsigned x)/KSup x) • gradient KSup x) := by
    filter_upwards [upperParameter_eventually_outer hx,self_mem_nhdsWithin] with t hq ht
    exact upperFlux_outer_affine ht hq
  have hc:ContinuousAt (fun t:ℝ=>κ • gradient Zsigned x+
      ((t-κ*Zsigned x)/KSup x) • gradient KSup x) (U x):=by fun_prop
  apply Tendsto.congr' he.symm
  simpa only [U_eq_signed_of_pos hx,sub_self,zero_div,zero_smul,add_zero,gradient_U_eq_signed hx] using
    hc.tendsto.mono_left nhdsWithin_le_nhds
end Bernoulli.DeSilvaJerison

end
end

end OAI

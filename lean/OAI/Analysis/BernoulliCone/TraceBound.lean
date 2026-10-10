import OAI.Analysis.BernoulliCone.ZeroTrace

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma radiusSq_zero_coordinate {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) : x 0=0 := by
  have ht:Cylindrical.transverse axis x=0:=by
    have hh:=Cylindrical.transverse_sq axis x axis_norm
    rw [hq] at hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
  have hh:=congrArg (fun y:Space 7=>y 0) ht
  simpa [Cylindrical.transverse,axis] using hh

lemma radiusSq_pos_ae : ∀ᵐ x:Space 7 ∂volume,0<Cylindrical.radiusSq axis x := by
  let e:Space 7:=EuclideanSpace.single 0 1
  let a:=innerSL ℝ e
  have he:e≠0:=by simp [e]
  have ha:a≠0:=by
    intro hh
    have hx:inner ℝ e e=0:=by
      have h:=congrArg (fun f:Space 7→L[ℝ]ℝ=>f e) hh
      simpa [a] using h
    exact he (inner_self_eq_zero.mp hx)
  have hker:volume (LinearMap.ker a.toLinearMap : Set (Space 7))=0:=by
    apply Measure.addHaar_submodule
    rw [Ne,LinearMap.ker_eq_top]
    intro hh
    exact ha (ContinuousLinearMap.coe_injective hh)
  have hne:∀ᵐ x:Space 7 ∂volume,x 0≠0:=by
    rw [ae_iff]
    change volume {x:Space 7 | inner ℝ e x=0}=0 at hker
    simpa [e,not_not,EuclideanSpace.inner_single_left] using hker
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (Cylindrical.radiusSq_nonneg axis x axis_norm)
    (fun h=>hx (radiusSq_zero_coordinate h.symm))

lemma boundary_signed_slope {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x=0) : ‖κ • gradient Zsigned x‖^2=1 := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hf:f (angle x)=0:=by
    rw [Zsigned_eq] at hz
    exact (mul_eq_zero.mp hz).resolve_left (norm_ne_zero_iff.mpr hx)
  have ht:|angle x|=t7:=root_unique ⟨abs_nonneg _,ha⟩ (by rwa [f_abs])
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Zsigned_boundary_slope hx ht,κ_sq]

lemma boundary_outer_eventually {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x=0) :
    ∀ᶠ t:ℝ in 𝓝[>] 0,(upperParameter x t)^2<Cylindrical.radiusSq axis x := by
  let l:=Real.sqrt (Cylindrical.radiusSq axis x)/2
  have hl:0<l:=by dsimp [l]; positivity
  have hlq:l^2<Cylindrical.radiusSq axis x:=by
    have hh:=Real.sq_sqrt hq.le
    dsimp [l]
    nlinarith
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hpos:0<capAmplitude*l^3*KSup x:=mul_pos (mul_pos capAmplitude_pos (pow_pos hl _)) (KSup_pos hx ha)
  have hF:0<upperFamily l x:=by
    rw [upperFamily_outer_formula hl hlq.le,hz,zero_add,max_eq_left hpos.le]
    exact mul_pos κ_pos hpos
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,hz,max_self,mul_zero]
  have hn:∀ᶠ t:ℝ in 𝓝[>] 0,t<upperFamily l x:=
    (gt_mem_nhds hF).filter_mono nhdsWithin_le_nhds
  filter_upwards [hn,self_mem_nhdsWithin] with t ht ht0
  have htt:U x<t:=by rwa [hU]
  have hh:upperParameter x t<l:=(upperParameter_lt_iff htt hl).mpr ht
  exact ((sq_lt_sq₀ (upperParameter_spec htt).1.le hl.le).mpr hh).trans hlq

lemma upperFlux_boundary_trace {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x=0) :
    Tendsto (fun t:ℝ=>upperFlux (x,t)) (𝓝[>] 0) (𝓝 (κ • gradient Zsigned x)) := by
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,hz,max_self,mul_zero]
  have he:(fun t:ℝ=>upperFlux (x,t)) =ᶠ[𝓝[>] 0]
      (fun t=>κ • gradient Zsigned x+(t/KSup x) • gradient KSup x):=by
    filter_upwards [boundary_outer_eventually hq hz,self_mem_nhdsWithin] with t ht ht0
    rw [upperFlux_outer_affine (by rwa [hU]) ht,hz,mul_zero,sub_zero]
  apply Tendsto.congr' he.symm
  have hc:ContinuousAt (fun t:ℝ=>κ • gradient Zsigned x+(t/KSup x) • gradient KSup x) 0:=by fun_prop
  simpa only [zero_div,zero_smul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- Full zero-phase upper trace bound, including the conical boundary. Only
the null axis is excluded; no assertion about the boundary's measure is used. -/
theorem upperFlux_zero_trace_bound {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hU:U x=0) {η:ℝ} (hη:0<η) :
    ∀ᶠ t:ℝ in 𝓝[>] 0,‖upperFlux (x,t)‖^2<1+η := by
  have hz:Zsigned x≤0:=by
    rw [U_eq_signed_pospart hq] at hU
    have hh:max (Zsigned x) 0=0:=(mul_eq_zero.mp hU).resolve_left κ_pos.ne'
    exact (le_max_left _ _).trans hh.le
  rcases hz.eq_or_lt with he|hl
  · have ht:=((upperFlux_boundary_trace hq he).norm.pow 2)
    rw [boundary_signed_slope hq he] at ht
    exact ht.eventually (gt_mem_nhds (by linarith : (1:ℝ)<1+η))
  · exact (upperFlux_eventually_subunit hq hl).mono fun _ h=>by linarith
end Bernoulli.DeSilvaJerison

end
end

end OAI

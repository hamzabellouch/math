import OAI.Analysis.BernoulliCone.CompactZeroFiber

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma exists_zero_upper_leaf {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x<0) : ∃l:ℝ,0<l ∧ upperFamily l x=0 := by
  have hc:ContinuousAt (fun l:ℝ=>Zsigned x+capAmplitude*l^3*KSup x) 0:=by fun_prop
  have hp:Zsigned x+capAmplitude*(0:ℝ)^3*KSup x<0:=by simpa using hz
  have hn:∀ᶠ l:ℝ in 𝓝[>] 0,Zsigned x+capAmplitude*l^3*KSup x<0:=
    (hc.eventually (gt_mem_nhds hp)).filter_mono nhdsWithin_le_nhds
  have hqn:∀ᶠ l:ℝ in 𝓝[>] 0,l^2<Cylindrical.radiusSq axis x:=
    ((continuousAt_id.pow 2).eventually (gt_mem_nhds (by simpa using hq))).filter_mono nhdsWithin_le_nhds
  have hn0:∀ᶠ l:ℝ in 𝓝[>] 0,0<l:=self_mem_nhdsWithin
  obtain ⟨l,hl,hlq,hlp⟩:=(hn0.and (hqn.and hn)).exists
  refine ⟨l,hl,?_⟩
  rw [upperFamily_outer_formula hl hlq.le,max_eq_right hlp.le,mul_zero]
lemma upperParameter_compact_near_zero {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x<0) : ∃a b:ℝ,0<a ∧ a≤b ∧
      ∀t:ℝ,0<t → t<1 → upperParameter x t∈Icc a b := by
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,max_eq_right hz.le,mul_zero]
  obtain ⟨a,ha,hea⟩:=exists_zero_upper_leaf hq hz
  let b:=upperParameter x 1
  have ht:U x<1:=by rw [hU]; norm_num
  have hb:0<b:=(upperParameter_spec ht).1
  have hab:a<b:=(lt_upperParameter_iff ht ha).mpr (by rw [hea]; norm_num)
  refine ⟨a,b,ha,hab.le,?_⟩
  intro t ht0 ht1
  have hUt:U x<t:=by rwa [hU]
  refine ⟨((lt_upperParameter_iff hUt ha).mpr (by rwa [hea])).le,?_⟩
  apply le_of_lt ((upperParameter_lt_iff hUt hb).mpr _)
  change t<upperFamily (upperParameter x 1) x
  rw [(upperParameter_spec ht).2]
  exact ht1
lemma upperTrace_continuousAt (x:Space 7) {l:ℝ} (hl:0<l) :
    ContinuousAt (upperTrace x) l := by
  exact ((continuousAt_const.mul continuousAt_id).mul
    (upperSigned_continuous.continuousAt.comp
      ((continuousAt_id.inv₀ hl.ne').smul continuousAt_const)))
lemma gradient_smoothCap_continuousAt {y:Space 7} (hq:Cylindrical.radiusSq axis y≤1) :
    ContinuousAt (gradient smoothCap) y := by
  have hh:ContDiffAt ℝ ∞ (gradient smoothCap) y:=
    (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp y
      ((smoothCap_contDiffAt hq).fderiv_right (by simp))
  exact hh.continuousAt
lemma gradient_outerSigned_continuousAt {y:Space 7} (hq:1≤Cylindrical.radiusSq axis y) :
    ContinuousAt (gradient outerSigned) y := by
  obtain ⟨hy,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis y by linarith)
  have hh:ContDiffAt ℝ ∞ (gradient outerSigned) y:=
    (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp y
      ((outerSigned_contDiffAt (n:=∞) hy ha).fderiv_right (by simp))
  exact hh.continuousAt
lemma scaled_gradient_norm_sq_continuousAt (x:Space 7) {l:ℝ} (hl:0<l)
    {W:Space 7→Space 7} (hW:ContinuousAt W (l⁻¹ • x)) :
    ContinuousAt (fun s:ℝ=>‖κ • W (s⁻¹ • x)‖^2) l := by
  have hc:ContinuousAt (fun s:ℝ=>s⁻¹ • x) l:=
    (continuousAt_id.inv₀ hl.ne').smul continuousAt_const
  have hg:ContinuousAt (fun s:ℝ=>W (s⁻¹ • x)) l:=
    ContinuousAt.comp (f:=fun s:ℝ=>s⁻¹ • x) (g:=W) hW hc
  exact (hg.const_smul κ).norm.pow 2
lemma normalized_radiusSq_ge_one {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2≤Cylindrical.radiusSq axis x) : 1≤Cylindrical.radiusSq axis (l⁻¹ • x) := by
  rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,le_div_iff₀ (sq_pos_of_pos hl),one_mul]
  exact hq

theorem upperFlux_eventually_subunit {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hz:Zsigned x<0) : ∀ᶠ t:ℝ in 𝓝[>] 0,‖upperFlux (x,t)‖^2<1 := by
  have hU:U x=0:=by rw [U_eq_signed_pospart hq,max_eq_right hz.le,mul_zero]
  obtain ⟨a,b,ha,hab,hpar⟩:=upperParameter_compact_near_zero hq hz
  let Kc:Set ℝ:=Icc a b ∩ {l|Cylindrical.radiusSq axis x≤l^2}
  let Ko:Set ℝ:=Icc a b ∩ {l|l^2≤Cylindrical.radiusSq axis x}
  have hKc:IsCompact Kc:=isCompact_Icc.inter_right (isClosed_le continuous_const (continuous_id.pow 2))
  have hKo:IsCompact Ko:=isCompact_Icc.inter_right (isClosed_le (continuous_id.pow 2) continuous_const)
  have hlc (l:ℝ)(hl:l∈Kc):0<l:=ha.trans_le hl.1.1
  have hlo (l:ℝ)(hl:l∈Ko):0<l:=ha.trans_le hl.1.1
  have hqc (l:ℝ)(hl:l∈Kc):Cylindrical.radiusSq axis (l⁻¹ • x)≤1:=
    (radiusSq_inv_smul_le_iff (hlc l hl) x).mpr hl.2
  have hqo (l:ℝ)(hl:l∈Ko):1≤Cylindrical.radiusSq axis (l⁻¹ • x):=
    normalized_radiusSq_ge_one (hlo l hl) hl.2
  have hs0(l:ℝ)(hl:0<l)(he:upperTrace x l=0):upperSigned (l⁻¹ • x)=0:=
    (mul_eq_zero.mp he).resolve_left (mul_pos κ_pos hl).ne'
  have hc:∀ᶠ t:ℝ in 𝓝 0,∀l∈Kc,upperTrace x l=t → ‖κ • gradient smoothCap (l⁻¹ • x)‖^2<1:=by
    apply Foliation.eventually_near_zero_fiber hKc
    · exact fun l hl=>upperTrace_continuousAt x (hlc l hl)
    · intro l hl
      exact scaled_gradient_norm_sq_continuousAt x (hlc l hl)
        (gradient_smoothCap_continuousAt (hqc l hl))
    · intro l hl he
      exact (upper_free_boundary_slopes (hs0 l (hlc l hl) he)).1 (hqc l hl)
  have ho:∀ᶠ t:ℝ in 𝓝 0,∀l∈Ko,upperTrace x l=t → ‖κ • gradient outerSigned (l⁻¹ • x)‖^2<1:=by
    apply Foliation.eventually_near_zero_fiber hKo
    · exact fun l hl=>upperTrace_continuousAt x (hlo l hl)
    · intro l hl
      exact scaled_gradient_norm_sq_continuousAt x (hlo l hl)
        (gradient_outerSigned_continuousAt (hqo l hl))
    · intro l hl he
      exact (upper_free_boundary_slopes (hs0 l (hlo l hl) he)).2 (hqo l hl)
  have htn:∀ᶠ t:ℝ in 𝓝[>] 0,t<1:=(gt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hc.filter_mono nhdsWithin_le_nhds,ho.filter_mono nhdsWithin_le_nhds,htn,self_mem_nhdsWithin] with t hct hot ht1 ht0
  have ht:U x<t:=by rwa [hU]
  have hl:0<upperParameter x t:=(upperParameter_spec ht).1
  have he:upperTrace x (upperParameter x t)=t := by
    have hh:=(upperParameter_spec ht).2
    rw [upperFamily_eq_max hl.le] at hh
    have hpos:0<upperTrace x (upperParameter x t):=by rw [←hh] at ht0; simpa using ht0
    rwa [max_eq_left hpos.le] at hh
  rw [upperFlux,ite_eq_left ht]
  split_ifs with hqc'
  · exact hct _ ⟨hpar t ht0 ht1,(radiusSq_inv_smul_le_iff hl x).mp hqc'⟩ he
  · have hqo':(upperParameter x t)^2≤Cylindrical.radiusSq axis x:=by
      have hh:¬Cylindrical.radiusSq axis x≤(upperParameter x t)^2:=by
        intro h; exact hqc' ((radiusSq_inv_smul_le_iff hl x).mpr h)
      exact (not_le.mp hh).le
    exact hot _ ⟨hpar t ht0 ht1,hqo'⟩ he
end Bernoulli.DeSilvaJerison

end
end

end OAI

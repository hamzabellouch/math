import OAI.Analysis.BernoulliCone.UpperFoliation

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma p_eq_max_f {t:ℝ} (ht:|t|<1) : p t=max (f t) 0 := by
  by_cases h:t7≤|t|
  · have hf:f t≤0 := by
      rw [←f_abs,←f_t7]
      exact f_strictAnti.antitoneOn ⟨t7_pos.le,t7_lt_one⟩ ⟨abs_nonneg t,ht⟩ h
    rw [p_eq_zero h,max_eq_right hf]
  · have hlt:|t|<t7:=lt_of_not_ge h
    rw [p_eq_f hlt.le,max_eq_left (f_pos_of_abs_lt hlt).le]
lemma U_eq_signed_pospart {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    U x=κ*max (Zsigned x) 0 := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  rw [U,Z,Zsigned_eq]
  change κ*(‖x‖*p (angle x))=κ*max (‖x‖*f (angle x)) 0
  rw [p_eq_max_f ha,mul_max_of_nonneg _ _ (norm_nonneg x),mul_zero]
lemma upperFamily_outer_formula {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2≤Cylindrical.radiusSq axis x) :
    upperFamily l x=κ*max (Zsigned x+capAmplitude*l^3*KSup x) 0 := by
  have hqp:0<Cylindrical.radiusSq axis x:=(sq_pos_of_pos hl).trans_le hq
  have hqt:1≤Cylindrical.radiusSq axis (l⁻¹ • x) := by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,le_div_iff₀ (sq_pos_of_pos hl),one_mul]
    exact hq
  rw [upperFamily,upperSigned_outer hqt,mul_assoc,mul_max_of_nonneg _ _ hl.le,mul_zero,
    outerSigned,Zsigned_smul x (inv_pos.mpr hl),KSup_smul hqp (inv_pos.mpr hl)]
  norm_num only [zpow_neg,zpow_ofNat,inv_inv]
  congr 2
  field_simp
lemma upperFamily_tendsto_zero_off_axis {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    Tendsto (fun l:ℝ=>upperFamily l x) (𝓝[>] 0) (𝓝 (U x)) := by
  have hc:ContinuousAt (fun l:ℝ=>κ*max (Zsigned x+capAmplitude*l^3*KSup x) 0) 0:=by fun_prop
  have he:(fun l:ℝ=>upperFamily l x)=ᶠ[𝓝[>] 0]
      (fun l:ℝ=>κ*max (Zsigned x+capAmplitude*l^3*KSup x) 0) := by
    have hsq:∀ᶠ l:ℝ in 𝓝[>] 0,l^2<Cylindrical.radiusSq axis x := by
      exact ((continuousAt_id.pow 2).eventually (gt_mem_nhds (by simpa using hq))).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsq,self_mem_nhdsWithin] with l hl hp
    exact upperFamily_outer_formula hp hl.le
  apply Tendsto.congr' he.symm
  simpa only [zero_pow (by norm_num:3≠0),mul_zero,zero_mul,add_zero,←U_eq_signed_pospart hq] using hc.tendsto.mono_left nhdsWithin_le_nhds
lemma U_zero_of_radiusSq_zero {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) : U x=0 := by
  apply le_antisymm _ (U_nonneg x)
  by_contra hn
  obtain ⟨hx,ha⟩:=(U_pos_iff x).mp (lt_of_not_ge hn)
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  have hs:|x 6|<‖x‖ := by
    have hh:=ha.trans t7_lt_one
    rw [angle,abs_div,abs_of_pos hn,div_lt_one hn] at hh
    exact hh
  have hs2: (x 6)^2<‖x‖^2:=by nlinarith [sq_abs (x 6),abs_nonneg (x 6)]
  simp only [Cylindrical.radiusSq,Cylindrical.axis,inner_axis] at hq
  linarith
lemma smoothCap_pos_zero : 0<smoothCap 0 := by
  change 0<CapAlgebra.Y (Cylindrical.radiusSq axis 0) capB capC*
    capH (Cylindrical.axis axis 0*(CapAlgebra.V (Cylindrical.radiusSq axis 0) capB)⁻¹)
  simp only [Cylindrical.radiusSq,Cylindrical.axis,norm_zero,inner_zero_left,zero_pow (by norm_num:2≠0),sub_zero,zero_mul]
  exact mul_pos (CapAlgebra.Y_pos (by norm_num)
    (CapAlgebra.V_bounds (by norm_num) (by norm_num) capB_bounds.1 capB_bounds.2).1 capC_pos)
    ((capH_pos_iff 0).mpr (by norm_num))
lemma smoothCap_le_at_zero {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) : smoothCap x ≤ smoothCap 0 := by
  have hh:∀s:ℝ,capH s≤capH 0 := by
    intro s
    rw [←capH_abs]
    exact capH_antitone (by norm_num) (abs_nonneg s) (abs_nonneg s)
  have hq0:Cylindrical.radiusSq axis (0:Space 7)=0:=by simp [Cylindrical.radiusSq,Cylindrical.axis]
  unfold smoothCap Cylindrical.lift
  rw [hq,hq0]
  simp only [Cylindrical.axis,inner_zero_left,zero_mul]
  exact mul_le_mul_of_nonneg_left (hh _) (CapAlgebra.Y_pos (by norm_num)
    (CapAlgebra.V_bounds (by norm_num) (by norm_num) capB_bounds.1 capB_bounds.2).1 capC_pos).le
lemma upperFamily_axis_bound {x:Space 7} (hq:Cylindrical.radiusSq axis x=0) {l:ℝ} (hl:0≤l) :
    upperFamily l x≤κ*l*smoothCap 0 := by
  have hqt:Cylindrical.radiusSq axis (l⁻¹ • x)=0:=by rw [Cylindrical.radiusSq_smul,hq,mul_zero]
  rw [upperFamily,upperSigned_cap (by rw [hqt]; norm_num)]
  exact mul_le_mul_of_nonneg_left (max_le (smoothCap_le_at_zero hqt) smoothCap_pos_zero.le) (mul_nonneg κ_pos.le hl)
lemma upperFamily_tendsto_zero (x:Space 7) :
    Tendsto (fun l:ℝ=>upperFamily l x) (𝓝[>] 0) (𝓝 (U x)) := by
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with hq|hq
  · rw [U_zero_of_radiusSq_zero hq.symm]
    apply squeeze_zero' (by filter_upwards [self_mem_nhdsWithin] with l hl; exact upperFamily_nonneg hl.le x)
      (by filter_upwards [self_mem_nhdsWithin] with l hl; exact upperFamily_axis_bound hq.symm hl.le)
    have hc:ContinuousAt (fun l:ℝ=>κ*l*smoothCap 0) 0:=by fun_prop
    simpa only [mul_zero,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · exact upperFamily_tendsto_zero_off_axis hq
end Bernoulli.DeSilvaJerison

end
end

end OAI

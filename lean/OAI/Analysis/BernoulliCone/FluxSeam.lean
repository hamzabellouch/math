import OAI.Analysis.BernoulliCone.FluxBulk

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma outerSigned_dilation_formula {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:0<Cylindrical.radiusSq axis x) :
    κ*l*outerSigned (l⁻¹ • x)=κ*(Zsigned x+capAmplitude*l^3*KSup x) := by
  rw [outerSigned,Zsigned_smul x (inv_pos.mpr hl),KSup_smul hq (inv_pos.mpr hl)]
  norm_num only [zpow_neg,zpow_ofNat,inv_inv]
  field_simp

lemma outerSigned_dilation_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:0<Cylindrical.radiusSq axis x) :
    κ • gradient outerSigned (l⁻¹ • x)=κ • gradient Zsigned x+
      (κ*capAmplitude*l^3) • gradient KSup x := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hqy:0<Cylindrical.radiusSq axis (l⁻¹ • x):=by rw [Cylindrical.radiusSq_smul]; positivity
  obtain ⟨hyn,hya⟩:=radiusSq_pos_data hqy
  have hdz:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have he:(fun y=>κ*l*outerSigned (l⁻¹ • y)) =ᶠ[𝓝 x]
      (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)):=by
    filter_upwards [((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt).eventually (lt_mem_nhds hq)] with y hy
    exact outerSigned_dilation_formula hl hy
  rw [←gradient_dilation hl.ne' ((outerSigned_contDiffAt (n:=1) hyn hya).differentiableAt (by simp)),gradient,he.fderiv_eq]
  change gradient (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) x=_
  have hdf:DifferentiableAt ℝ (fun y=>Zsigned y+capAmplitude*l^3*KSup y) x:=
    hdz.add (hdk.const_mul (capAmplitude*l^3))
  rw [gradient_const_mul κ hdf,gradient_add' hdz (hdk.const_mul (capAmplitude*l^3)),
    gradient_const_mul (capAmplitude*l^3) hdk,smul_add,smul_smul]
  congr 2
  ring

lemma seamHeight_signed_dilation {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    seamHeight x=κ*Real.sqrt (Cylindrical.radiusSq axis x)*
      outerSigned ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  rw [outerSigned_at_seam (normalized_radius_seam hq),seamHeight_formula,Cylindrical.axis_smul,div_eq_mul_inv,mul_comm (Cylindrical.axis axis x)]

lemma exteriorFlux_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    exteriorFlux (x,seamHeight x)=
      κ • gradient outerSigned ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  let l:=Real.sqrt (Cylindrical.radiusSq axis x)
  have hl:0<l:=Real.sqrt_pos.mpr hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have he:seamHeight x=κ*(Zsigned x+capAmplitude*l^3*KSup x):=by
    rw [seamHeight_signed_dilation hq]
    exact outerSigned_dilation_formula hl hq
  rw [outerSigned_dilation_gradient hl hq]
  unfold exteriorFlux
  dsimp only
  rw [he]
  congr 1
  congr 1
  apply (div_eq_iff (KSup_pos hx ha).ne').mpr
  ring

lemma upperParameter_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hp:U x<seamHeight x) : upperParameter x (seamHeight x)=Real.sqrt (Cylindrical.radiusSq axis x) := by
  exact (upperParameter_unique hp (Real.sqrt_pos.mpr hq)
    ((upperFamily_at_seam hq).trans (max_eq_left ((U_nonneg x).trans hp.le))))

lemma upperFlux_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hp:U x<seamHeight x) : upperFlux (x,seamHeight x)=
      κ • gradient smoothCap ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  rw [upperFlux,ite_eq_left hp,upperParameter_at_seam hq hp,
    ite_eq_left (normalized_radius_seam hq).le]

theorem upperFlux_seam_jump {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hp:U x<seamHeight x) :
    ‖upperFlux (x,seamHeight x)‖^2-‖exteriorFlux (x,seamHeight x)‖^2-
      2*inner ℝ (upperFlux (x,seamHeight x)-exteriorFlux (x,seamHeight x)) (gradient seamHeight x)≤0 := by
  rw [upperFlux_at_seam hq hp,exteriorFlux_at_seam hq,gradient_seamHeight hq]
  apply upperCalibration_seam (normalized_radius_seam hq)
  have hh:0<seamHeight x:=(U_nonneg x).trans_lt hp
  rw [seamHeight_signed_dilation hq,←upper_seam_agreement (normalized_radius_seam hq)] at hh
  exact pos_of_mul_pos_right hh (mul_nonneg κ_pos.le (Real.sqrt_nonneg _))
end Bernoulli.DeSilvaJerison

end
end

end OAI

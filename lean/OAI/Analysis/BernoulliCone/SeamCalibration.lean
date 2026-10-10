import OAI.Analysis.BernoulliCone.FoliationSeam

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma polarGradient_span (x:Space 7) (a b:ℝ) :
    ∃c d:ℝ,polarGradient axis x a b=c • axis+d • x := by
  refine ⟨b,(a-b*(inner ℝ x axis/‖x‖))*‖x‖⁻¹,?_⟩
  unfold polarGradient radial
  module
lemma outerGradient_span {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    ∃a b:ℝ,gradient outerSigned x=a • axis+b • x := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hdz:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hz:gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
    have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by
      simpa only [mem_Ioo,inner_axis,angle] using (show -1<angle x ∧ angle x<1 from abs_lt.mp ha)
    rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
    simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
  obtain ⟨a,b,hab⟩:=polarGradient_span x (f (angle x)) (fp (angle x))
  obtain ⟨c,d,hcd⟩:=polarGradient_span x (-2*gSup (angle x)) (gSup1 (angle x))
  change ∃a b:ℝ,gradient (fun x=>Zsigned x+capAmplitude*KSup x) x=a • axis+b • x
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,hz,
    KSup_gradient hx ha,hab,hcd]
  refine ⟨a+capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)*c,b+capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)*d,?_⟩
  module
lemma cylindrical_projection {x G:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    (hG:∃a b:ℝ,G=a • axis+b • x) :
    G=inner ℝ G axis • axis+inner ℝ G (Cylindrical.transverse axis x) • Cylindrical.transverse axis x := by
  obtain ⟨a,b,hab⟩:=hG
  have hn:inner ℝ (Cylindrical.transverse axis x) axis=0:=Cylindrical.transverse_inner axis x axis_norm
  have hn':inner ℝ axis (Cylindrical.transverse axis x)=0:=by rw [real_inner_comm,hn]
  have hnn:inner ℝ (Cylindrical.transverse axis x) (Cylindrical.transverse axis x)=1:=by
    rw [real_inner_self_eq_norm_sq,Cylindrical.transverse_sq axis x axis_norm,hq]
  have hg:G=(a+b*Cylindrical.axis axis x) • axis+b • Cylindrical.transverse axis x:=by
    rw [hab,Cylindrical.transverse]
    module
  rw [hg]
  simp only [inner_add_left,real_inner_smul_left,hn,hn',hnn,mul_zero,mul_one,zero_add,add_zero,
    real_inner_self_eq_norm_sq,axis_norm,one_pow]

lemma smoothCap_gradient_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    gradient smoothCap x=capHP (Cylindrical.axis axis x) • axis+
      (capEta*capH (Cylindrical.axis axis x)-
        capP*Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)) • Cylindrical.transverse axis x := by
  rw [gradient_smoothCap (le_of_eq hq)]
  simp only [hq,CapAlgebra.V_one,CapAlgebra.Y_one,CapAlgebra.D_one,CapAlgebra.Y1_one,
    div_one,one_pow,inv_one,one_mul]
  module
lemma outer_gradient_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    gradient outerSigned x=capHP (Cylindrical.axis axis x) • axis+
      (capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)-
        3*capAmplitude*(1+2*(Cylindrical.axis axis x)^2)) • Cylindrical.transverse axis x := by
  rw [cylindrical_projection hq (outerGradient_span (by rw [hq]; norm_num)),
    outerSigned_axis_at_seam hq,outerSigned_transverse_at_seam hq]
/-- Tangential matching gives the gradient of the one-homogeneous seam height. -/
def seamGradient (x:Space 7) : Space 7 :=
  capHP (Cylindrical.axis axis x) • axis+
    (capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)) •
      Cylindrical.transverse axis x
lemma seamGradient_matching {x G:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    {b:ℝ} (hg:G=capHP (Cylindrical.axis axis x) • axis+b • Cylindrical.transverse axis x) :
    seamGradient x=G+(capH (Cylindrical.axis axis x)-inner ℝ x G) • Cylindrical.transverse axis x := by
  have hn:inner ℝ x (Cylindrical.transverse axis x)=1:=by
    rw [Cylindrical.transverse,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    change ‖x‖^2-Cylindrical.axis axis x*Cylindrical.axis axis x=1
    simpa only [Cylindrical.radiusSq,pow_two] using hq
  rw [hg]
  simp only [inner_add_right,real_inner_smul_right,hn,mul_one]
  change seamGradient x=_
  unfold seamGradient Cylindrical.axis
  module

/-- The actual cap/exterior calibration has the required nonpositive seam flux.
This verifies the jump, rather than inserting a comparison premise. -/
theorem upperCalibration_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    (hp:0<smoothCap x) :
    ‖κ • gradient smoothCap x‖^2-‖κ • gradient outerSigned x‖^2-
      2*inner ℝ (κ • gradient smoothCap x-κ • gradient outerSigned x) (κ • seamGradient x)≤0 := by
  have ha:|Cylindrical.axis axis x|<3/4 := by
    rw [smoothCap_at_seam hq] at hp
    exact (capH_pos_iff _).mp hp
  have hoc:0<outerSigned x:=by rwa [←upper_seam_agreement hq]
  obtain ⟨hx,ht⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by rw [hq]; norm_num)
  let ρc:=κ*(smoothCap x-inner ℝ x (gradient smoothCap x))
  let ρo:=κ*(outerSigned x-inner ℝ x (gradient outerSigned x))
  have hρc:0<ρc:=mul_pos κ_pos (smoothCap_radial_defect_pos (le_of_eq hq) hp)
  have hρo:0<ρo:=mul_pos κ_pos (outerSigned_radial_defect_pos hx ht)
  have hc:κ • seamGradient x=κ • gradient smoothCap x+ρc • Cylindrical.transverse axis x := by
    rw [seamGradient_matching hq (smoothCap_gradient_at_seam hq),smul_add,smul_smul]
    dsimp only [ρc]
    rw [smoothCap_at_seam hq]
  have ho:κ • seamGradient x=κ • gradient outerSigned x+ρo • Cylindrical.transverse axis x := by
    rw [seamGradient_matching hq (outer_gradient_at_seam hq),smul_add,smul_smul]
    dsimp only [ρo]
    rw [outerSigned_at_seam hq]
  apply Foliation.seam_flux_nonpos _ _ _ _ ρc ρo hc ho (add_nonneg hρc.le hρo.le)
  rw [←smul_sub,real_inner_smul_left,inner_sub_left]
  have hj:=upper_seam_jump hq ha.le
  rw [inner_sub_left] at hj
  exact mul_nonneg κ_pos.le (by linarith)
end Bernoulli.DeSilvaJerison

end
end

end OAI

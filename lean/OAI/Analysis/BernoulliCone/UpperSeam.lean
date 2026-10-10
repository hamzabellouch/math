import OAI.Analysis.BernoulliCone.StrictSlope

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
lemma axis_add_axis {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (he:‖e‖=1) (t:ℝ) : axis e (x+t • e)=axis e x+t := by
  simp [axis,inner_add_left,real_inner_smul_left,he]
lemma radiusSq_add_axis {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (he:‖e‖=1) (t:ℝ) : radiusSq e (x+t • e)=radiusSq e x := by
  simp only [radiusSq,axis_add_axis e x he,norm_add_sq_real,norm_smul,
    Real.norm_eq_abs,sq_abs,he,mul_one,real_inner_smul_right]
  unfold axis
  ring
end Bernoulli.Cylindrical
namespace Bernoulli.DeSilvaJerison
lemma cap_boundary_slope_lt : capC^2*(capHP (3/4))^2<c7 := by
  have hp := capP_bounds
  have ha := capAmplitude_bounds
  have hs : capP^2≤(3886/10000:ℝ)^2 := by nlinarith [hp.1,hp.2]
  have hq : 0≤3125/768-capAmplitude/6 := by linarith [ha.2]
  have hq1 : (3125/768-capAmplitude/6)^2≤(3125/768-(289237/1000000)/6:ℝ)^2 := by
    nlinarith [ha.1]
  rw [capC_sq,capHP_end]
  have hprod := mul_le_mul (show 1+9/16*capP^2≤1+9/16*(3886/10000:ℝ)^2 by linarith)
    hq1 (sq_nonneg _) (by positivity : (0:ℝ)≤1+9/16*(3886/10000:ℝ)^2)
  nlinarith only [hprod,c7_lower]
lemma smoothCap_boundary_slope_lt {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|=3/4) :
    ‖gradient smoothCap x‖^2<c7 := by
  rw [smoothCap_boundary_gradient hx hs]
  exact cap_boundary_slope_lt

namespace CapAlgebra
lemma V_one (b:ℝ) : V 1 b=1 := by unfold V; ring
lemma D_one : D 1 capB=capP := by unfold D capB; ring
lemma E_one : E 1 capB=capP-3/25 := by unfold E capB; ring
lemma H_one : H 1 capB=capC^2 := by rw [H,D_one,capC_sq]; ring
lemma Y_one : Y 1 capB capC=1 := by
  rw [Y,V_one,H_one,Real.sqrt_sq capC_pos.le,mul_one,div_self capC_pos.ne']
lemma Y1_one : 2*Y1 1 capB capC=capEta := by
  rw [Y1_eq (H_pos (by norm_num)) (by rw [V_one]; norm_num),Y_one,V_one,D_one,E_one,H_one,capC_sq]
  simp only [one_mul,div_one,capEta]
end CapAlgebra

lemma smoothCap_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    smoothCap x=capH (Cylindrical.axis axis x) := by
  simp only [smoothCap,Cylindrical.lift,hq,CapAlgebra.Y_one,CapAlgebra.V_one,inv_one,mul_one,one_mul]
lemma upper_seam_agreement {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    smoothCap x=outerSigned x := by rw [smoothCap_at_seam hq,outerSigned_at_seam hq]

lemma outerSigned_axis_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    inner ℝ (gradient outerSigned x) axis=capHP (Cylindrical.axis axis x) := by
  have hqp:0<Cylindrical.radiusSq axis x:=by rw [hq]; norm_num
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  rw [←ScalarLaplacian.line_deriv ((outerSigned_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)) axis]
  have he : (fun t:ℝ=>outerSigned (x+t • axis))=fun t=>capH (Cylindrical.axis axis x+t) := by
    funext t
    rw [outerSigned_at_seam (by rw [Cylindrical.radiusSq_add_axis axis x axis_norm,hq]),
      Cylindrical.axis_add_axis axis x axis_norm]
  rw [he]
  have hh:HasDerivAt (fun t:ℝ=>capH (Cylindrical.axis axis x+t)) (capHP (Cylindrical.axis axis x)) 0 := by
    convert! (hasDerivAt_capH (Cylindrical.axis axis x+0)).comp 0 ((hasDerivAt_id 0).const_add (Cylindrical.axis axis x)) using 1
    simp
  exact hh.deriv

lemma outerSigned_transverse_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    inner ℝ (gradient outerSigned x) (Cylindrical.transverse axis x)=
      capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)-
        3*capAmplitude*(1+2*(Cylindrical.axis axis x)^2) := by
  have hqp:0<Cylindrical.radiusSq axis x:=by rw [hq]; norm_num
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hh:=outerSigned_radial_defect hx ha
  rw [outerSigned_at_seam hq,KSup_cylindrical hqp,hq] at hh
  norm_num only [one_pow,div_one] at hh
  rw [Cylindrical.transverse,inner_sub_right,real_inner_smul_right,outerSigned_axis_at_seam hq,
    real_inner_comm x (gradient outerSigned x)]
  linarith

lemma smoothCap_transverse_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    inner ℝ (gradient smoothCap x) (Cylindrical.transverse axis x)=
      capEta*capH (Cylindrical.axis axis x)-
        capP*Cylindrical.axis axis x*capHP (Cylindrical.axis axis x) := by
  have he:inner ℝ axis (Cylindrical.transverse axis x)=0 := by
    rw [real_inner_comm,Cylindrical.transverse_inner axis x axis_norm]
  have ht:inner ℝ (Cylindrical.transverse axis x) (Cylindrical.transverse axis x)=1 := by
    rw [real_inner_self_eq_norm_sq,Cylindrical.transverse_sq axis x axis_norm,hq]
  rw [gradient_smoothCap (le_of_eq hq)]
  simp only [hq,CapAlgebra.V_one,CapAlgebra.Y_one,CapAlgebra.D_one,CapAlgebra.Y1_one,
    div_one,one_pow,inv_one,one_mul,inner_add_left,real_inner_smul_left,he,ht,mul_zero,mul_one,zero_add]
  ring

/-- Actual normal derivative jump of the glued Euclidean supersolution. -/
theorem upper_seam_jump {x:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    (ha:|Cylindrical.axis axis x|≤3/4) :
    inner ℝ (gradient outerSigned x-gradient smoothCap x) (Cylindrical.transverse axis x)≤0 := by
  rw [inner_sub_left,outerSigned_transverse_at_seam hq,smoothCap_transverse_at_seam hq]
  have he : capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)-
      3*capAmplitude*(1+2*(Cylindrical.axis axis x)^2)-
      (capEta*capH (Cylindrical.axis axis x)-capP*Cylindrical.axis axis x*capHP (Cylindrical.axis axis x))=
        capW (Cylindrical.axis axis x) := by unfold capW; ring
  rw [he]
  exact cap_interface_nonpos ha
end Bernoulli.DeSilvaJerison

end
end

end OAI

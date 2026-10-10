import OAI.Geometry.Convex.GeneralMahler.DefectIBP
import OAI.Geometry.Convex.GeneralMahler.EntropyMap

namespace OAI
/-! Entropy scalar simplification. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Layers Profile
lemma c_mul_p (x:ℝ) : MillsC x*p x=phi x := by unfold MillsC; field_simp [ne_of_gt (p_pos x)]
lemma cR_v (x:ℝ) : MillsC (-x)=2*a x-p x*deriv Profile.v x := by
  rw [v_deriv]
  unfold MillsJ a
  have h := c_mul_p x
  have he := c_mul_p (-x)
  rw [neg_phi,neg_p] at he; linarith

lemma LC_average : (∫ x,phi x*LC x)= logN0 + 1/2 := by
  have hi : Integrable (fun x:ℝ=>phi x*x^2) :=
    (rapid_phi.product (PolyBound.id.pow 2)).integrable_real
      ((c_phi.mul (continuous_id.pow 2)).measurable)
  have hh : (∫ x:ℝ,phi x*x^2)=1 := by
    have ht (x:ℝ) : HasDerivAt (fun x:ℝ=>phi x*x) (phi x-phi x*x^2) x := by
      convert (d_phi x).fun_mul (hasDerivAt_id' x) using 1; first | rfl | ring
    have ha := rapid_ftc (rapid_phi.product PolyBound.id) ht (i_phi.sub hi)
    rw [integral_sub i_phi hi,e_phi] at ha; linarith
  have he (x:ℝ) : phi x*LC x= logN0*phi x-phi x*x^2/2-phi x*LP x := by
    unfold LC MillsC; rw [Real.log_div (phi_pos _).ne' (p_pos _).ne']
    have hf : Real.log (phi x)=logN0-x^2/2 := by
      unfold logN0; rw [phi_apply,Real.log_mul (by positivity) (by positivity),Real.log_exp]; ring
    rw [hf]; unfold LP; ring
  simp_rw [he]
  rw [integral_sub,integral_sub,integral_const_mul,integral_div,e_phi,hh,logp_average]
  · ring
  all_goals first | exact i_phi.const_mul _ | exact hi.div_const _ | exact int_lp |
    exact (i_phi.const_mul _).sub (hi.div_const _)

lemma rapid_ca_prod : rapid fun x=>MillsC x*a x := by
  convert (rapid_mcs.product poly_a).rfadd (rapid_half_a.product poly_mc) using 1
  ext x; ring
lemma rapid_wa : rapid fun x=>MillsW x*a x := by
  convert rapid_ca_prod.product poly_mj using 1
  ext x; unfold MillsW; ring
lemma int_wa : Integrable fun x=>MillsW x*a x :=
  rapid_wa.integrable_real (c_mw.mul ca).measurable
lemma wa_area : (∫ x,MillsW x*a x)=1 := by
  have hd (x:ℝ) : HasDerivAt (fun x=>MillsC x*a x) (phi x - MillsW x*a x) x := by
    convert (d_mc x).fun_mul (d_a x) using 1
    all_goals first | rfl | (rw [c_mul_p]; ring)
  have hh := rapid_ftc rapid_ca_prod hd (i_phi.sub int_wa)
  rw [integral_sub i_phi int_wa,e_phi] at hh; linarith

variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m)
def cBy := ∫ x,MillsW (-x)*q.Bt x

lemma rapid_cdBy : rapid fun x=>MillsC (-x)*q.dB x := by
  have h : rapid (fun x=>MillsC (-x)*(1-st x)) := by
    intro n
    obtain ⟨C,hc,h⟩ := rapid_mcs n
    refine ⟨C,hc,fun x=>?_⟩
    specialize h (-x)
    unfold st at *
    dsimp at h ⊢
    split_ifs with hx
    · simp [hc]
    · have he : 0≤ -x := by linarith
      simpa [hx,he] using h
  convert (q.dB_tail.product mc_test.ref.poly).rfadd (h.product q.dB_poly) using 1
  ext x; ring
lemma i_wdB : Integrable (fun x=>MillsW (-x)*q.dB x) := by
  have h := q.rapid_cdBy.product mj_test.ref.poly
  have hh : rapid (fun x=>MillsW (-x)*q.dB x) := by convert h using 1; ext; unfold MillsW; ring
  exact hh.integrable_real (((c_mw.comp continuous_neg).mul q.dB_c).measurable)
lemma i_ca_neg : Integrable (fun x:ℝ=> MillsW (-x)*a (-x)) :=
  (measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding |>.mpr int_wa

lemma cBy_eq :
    q.delt d=q.cBy-q.s0+(∫ x,q.dm x*Profile.v x) := by
  have hi (x:ℝ) : HasDerivAt (fun x=>MillsC (-x)*q.dB x)
      (MillsW (-x)*q.dB x-(2*(a x*q.dr x)-p x*q.dr x*deriv Profile.v x)) x := by
    convert (((d_mc (-x)).comp x (hasDerivAt_neg' x)).fun_mul (q.dB_d x)) using 1
    all_goals first | rfl | (simp only [Function.comp_apply]; rw [cR_v]; ring)
  have ig : Integrable (fun x=>p x*q.dr x*deriv Profile.v x) :=
    q.prDelta_moment.int_test v_test.der
  have ih : Integrable (fun x=>2*(a x*q.dr x)) := q.arDelta_moment.inte.const_mul _
  have hh := rapid_ftc q.rapid_cdBy hi (q.i_wdB.sub (ih.sub ig))
  rw [integral_sub,integral_sub ih ig,integral_const_mul,q.mass.2] at hh
  · have he (x:ℝ) : MillsW (-x)*q.Bt x=MillsW (-x)*q.dB x+q.s0*(MillsW (-x)*a (-x)) := by
      unfold dB; ring
    have hx := integral_neg_eq_self (fun x=>MillsW x*a x) volume
    change (∫ x,MillsW (-x)*a (-x))=_ at hx
    unfold cBy; simp_rw [he]
    rw [integral_add q.i_wdB (i_ca_neg.const_mul _), integral_const_mul,hx,wa_area,
      q.delta_d,q.hd_test v_test]
    unfold rk
    simp_rw [add_mul]
    rw [integral_add ig (q.hd_m.int_test v_test.der)]
    linarith
  all_goals first | exact q.i_wdB | exact ih.sub ig

omit [NeZero m] in
lemma cost_eq (q:Scatter m) (v:Rn m) :
    q.cost v= ∫ z,MillsW z*⟪v,∫ x,q.y z x ∂normal m⟫ := by
  let l : Rn m→L[ℝ]ℝ := innerSL ℝ v
  have hi := l.integrable_comp q.Ki
  have hp (x) : ⟪v,q.t x⟫ = ∫ z,l (q.ky z x) := (l.integral_comp_comm (q.ki _)).symm
  unfold Scatter.cost; simp_rw [hp]
  rw [integral_integral_swap]
  · congr 1
    ext z
    have hh : Integrable (q.y z) (normal m) :=
      (PolyBound.lipschitz (q.yl z)).gaussian_integrable (q.yl z).continuous.aestronglyMeasurable
    rw [l.integral_comp_comm (show Integrable (q.ky z) (normal m) from hh.smul (MillsW z))]
    unfold Scatter.ky; rw [integral_smul,_root_.map_smul]; rfl
  have he : Integrable (fun u:ℝ×Rn m=>l (q.ky u.1 u.2)) (volume.prod (normal m)) := hi
  exact he.swap

lemma X_cost : q.primalMap.cost q.V=(m:ℝ) := by
  rw [cost_eq]
  simp_rw [q.X_sc,q.XT_mean,real_inner_smul_right]
  rw [real_inner_comm q.U,q.ip]
  simp_rw [← mul_assoc]; rw [integral_mul_const,wa_area]; ring

lemma Y_cost : q.dualMap.cost q.U=q.cBy*m := by
  rw [cost_eq]
  simp_rw [q.Y_sc]
  have H (z:ℝ) : ⟪q.U,∫ x,q.YT z x ∂normal m⟫=q.Bt z*m := by
    unfold Bt; have h:= m_pos (m:=m); field_simp
  simp_rw [H,← mul_assoc]; rw [integral_mul_const]
  have he := integral_neg_eq_self (fun x=>MillsW (-x)*q.Bt x) volume
  simp only [neg_neg] at he; rw [he]; rfl
end ProjField
end GeneralMahler

end

end OAI

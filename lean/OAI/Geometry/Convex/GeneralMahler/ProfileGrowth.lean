import OAI.Geometry.Convex.GeneralMahler.Profiles
import OAI.Geometry.Convex.GeneralMahler.TestFun

namespace OAI
/-! Profile regularity by derivative recurrences and log tail bounds. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
namespace GeneralMahler.Profile
open Layers

lemma Y_limitbound (x:ℝ) (hx:0≤x) : Y x ≤ (MillsC 0)⁻¹ := by
  have h : MillsC 0 ≤ MillsC (-x) := mc_anti.antitone (by linarith)
  have he : Y x=(MillsC (-x))⁻¹ := by unfold Y MillsC; rw [neg_p,neg_phi,inv_div]
  rw [he]
  apply (inv_le_inv₀ (mc_pos _) (mc_pos _)).mpr h
lemma f_poly : PolyBound f :=
  (((PolyBound.const 1).sub (PolyBound.of_bound (f:=p) 1 (fun x=>by
    rw [Real.norm_of_nonneg (p_pos x).le]; exact (p_lt_one x).le))).neg).sub poly_lp
lemma f_bounds (x:ℝ) : 0 ≤ f x ∧ f x ≤ (1-p x)^2/p x := by
  have hp := p_pos x
  have hh := Real.log_le_sub_one_of_pos hp
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hi
  unfold f
  constructor
  · linarith
  calc
    _ ≤ -(1-p x)+(p x)⁻¹-1 := by linarith
    _ = _ := by field_simp; ring

lemma X2f_poly : PolyBound fun x=> X x^2*f x := by
  obtain ⟨C,n,hc,h⟩ := f_poly
  set b := (MillsC 0)⁻¹
  have hb : 0≤b := (inv_pos.mpr (mc_pos _)).le
  refine ⟨b^2*(C+1),n,by positivity,fun x=>?_⟩
  have hh := f_bounds x
  have hp := xp x
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg (X x)) hh.1)]
  by_cases hx:0≤x
  · have hy := Y_limitbound x hx
    have hf : X x^2*f x ≤ b^2 := calc
      _ ≤ X x^2*((1-p x)^2/p x) :=
        mul_le_mul_of_nonneg_left hh.2 (by positivity)
      _ = p x*Y x^2 := by unfold X Y; have h:=p_pos x; field_simp
      _ ≤ b^2 := by
        have h' := yp x
        nlinarith [mul_le_of_le_one_left (sq_nonneg (Y x)) (p_lt_one x).le]
    have h' : (1:ℝ) ≤ (1+‖x‖)^n := one_le_pow₀ (by simp)
    apply hf.trans
    apply le_trans _ (show b^2*(C+1) ≤ _ from le_mul_of_one_le_right (by positivity) h')
    nlinarith
  · have hi := Y_limitbound (-x) (by linarith)
    rw [Y_ref] at hi
    have he := h x
    rw [Real.norm_of_nonneg hh.1] at he
    apply le_trans (mul_le_mul (show X x^2 ≤ b^2 by gcongr) he hh.1 (sq_nonneg _))
    rw [← mul_assoc]; gcongr; linarith
lemma Y2j_poly : PolyBound fun x=>Y x^2*j x := by
  have he := X2f_poly.comp PolyBound.id.neg
  simpa only [← Y_ref,← j_ref,neg_neg] using he
lemma X_M (x:ℝ) : Xd x=MillsJ x*X x := by
  unfold Xd X MillsJ MillsC; have h:=phi_pos x; have h':=p_pos x
  field_simp; ring
lemma Y_M (x:ℝ) : Yd x= -MillsJ (-x)*Y x := by
  have h := X_M (-x)
  rw [Xd,← Y_ref,neg_neg] at h
  unfold Yd; linarith
lemma g_poly : PolyBound g := by
  simp only [funext (show ∀ x,g x=(2:ℝ)⁻¹*(1-X x^2*f x-Y x^2*j x) from
    fun x=>by unfold g; ring)]
  exact (PolyBound.const _).mul (((PolyBound.const _).sub X2f_poly).sub Y2j_poly)
lemma gd_poly : PolyBound gd := by
  let H := fun x=>MillsJ (-x)*(Y x^2*j x)-MillsJ x*(X x^2*f x)
  have he : gd=H := by ext x; unfold gd H; rw [X_M,Y_M]; ring
  rw [he]
  exact ((TestF.poly mj_test.ref).mul Y2j_poly).sub (poly_mj.mul X2f_poly)
lemma d_poly : PolyBound d := by
  let H := fun x=>MillsJ x^2*(X x^2*f x)+MillsJ (-x)^2*(Y x^2*j x)
  have he : d=H := by ext x; unfold d H; rw [X_M,Y_M]; ring
  rw [he]
  exact ((poly_mj.pow 2).mul X2f_poly).add (((TestF.poly mj_test.ref).pow 2).mul Y2j_poly)

lemma v_test : TestF v := TestF.of_d dV (mj_test.sub mj_test.ref)
lemma moderate_dg (n : ℕ) :
    Moderate n g ∧ Moderate n (deriv g) ∧ Moderate n d := by
  induction n with
  | zero=>
    refine ⟨⟨g_poly,?_⟩,⟨?_,?_⟩,⟨d_poly,?_⟩⟩
    · exact continuous_iff_continuousAt.mpr fun x=>(dg x).continuousAt
    · rw [show deriv g=gd from funext fun x=>(dg x).deriv]; exact gd_poly
    · exact continuous_iff_continuousAt.mpr fun x=>(ddg x).continuousAt
    exact continuous_iff_continuousAt.mpr fun x=>(dd x).continuousAt
  | succ n ih=>
    obtain ⟨h,h',hi⟩ := ih
    refine ⟨Moderate.mk' (g:=deriv g) (fun x=>(dg x).differentiableAt.hasDerivAt) h',
      Moderate.mk' ddg ?_,Moderate.mk' dd ?_⟩
    · exact (((Moderate.id n).mul h').add ((Moderate.const _ n).mul h)).sub hi
    exact (((((Moderate.const _ n).mul (Moderate.id n)).mul hi).sub (TestF.der v_test n)).sub
      ((Moderate.const _ n).mul h'))
lemma g_test : TestF g := fun n=>(moderate_dg n).1
lemma d_test : TestF d := fun n=>(moderate_dg n).2.2
end GeneralMahler.Profile

end

end OAI

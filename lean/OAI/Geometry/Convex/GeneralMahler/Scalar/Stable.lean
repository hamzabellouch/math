import OAI.Geometry.Convex.GeneralMahler.Scalar.Moments
import OAI.Geometry.Convex.GeneralMahler.Scalar.HSeries
import OAI.Geometry.Convex.GeneralMahler.Packet

namespace OAI
/-! §07 stable algebra shared by finite and infinite estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
open Profile Layers
def sY:=Ymk 0
def sB:=Ymk 1
def sU (x:ℝ):=sY x*phi x
def sP (x:ℝ):=1-sU x
def sJ (x:ℝ):= x*x/2+Real.log (√(2*π))-Real.log (sY x)-sP x
def sH (x:ℝ):= Qh 0 (sU x)
def sW (x:ℝ):=1-sP x*sB x
def sd (x:ℝ):= sB x*sB x*sJ x+sW x*sW x*sH x
def sK (x:ℝ):= sd x+sY x*sY x*(sJ x+sP x*sP x*sH x)-1
def sg1 (x:ℝ):=sY x*(sB x*sJ x-sW x*sP x*sH x)
def sC (x:ℝ):= -(sd x)+(ar-1)*(x*sg1 x-sK x)
def sRv (x:ℝ):= phi x/sP x - sB x/sY x
def sV2 (x:ℝ):= let m:=phi x/sP x; 2-m*(x+m)-sB x/(sY x*sY x)
lemma u_eq' (x:ℝ) : sU x=1-p x := by
  unfold sU sY; rw [Ym0]; unfold Y; rw [div_mul_cancel₀ _ (phi_pos x).ne']
lemma u_pos (x:ℝ):0<sU x := by rw [u_eq']; linarith [p_lt_one x]
lemma u_le (x:ℝ):sU x<1 := by rw [u_eq']; linarith [p_pos x]
lemma sPe (x): sP x=p x := by rw [sP,u_eq']; ring
lemma h_f (x:ℝ): f x=sU x^2*sH x := by
  have h:= hlog (u_pos x) (u_le x)
  unfold f sH; rw [h,u_eq']; simp; ring
lemma lp_st (x:ℝ): sJ x=j x := by
  unfold sJ j
  rw [sPe,← u_eq',sU,Real.log_mul (show sY x≠0 from (Ymp _ _).ne') (phi_pos _).ne',phi_apply,
    Real.log_mul (by positivity) (by positivity),Real.log_inv,Real.log_exp]
  ring
lemma B_st (x): sB x=1-x*sY x := by unfold sB sY; linarith [R0 x]
lemma Xu (x): X x*sU x=sP x*sY x := by
  rw [sU,sPe]; unfold X; field_simp [(phi_pos x).ne']
lemma X1u (x): Xd x*sU x=sW x := by
  unfold Xd sW
  rw [add_mul,mul_assoc,Xu,B_st]; unfold sP; ring
lemma YDst (x): Yd x= -sB x := by unfold Yd; rw [B_st]; unfold sY; rw [Ym0]; ring
lemma d_stable (x:ℝ) : sd x=d x := by
  unfold sd d; rw [lp_st,← X1u,YDst,h_f]; ring
lemma k_stable (x:ℝ) : sK x=Kp x := by
  unfold Kp g sK; rw [d_stable,lp_st,h_f]
  have hh (x):sY x=Y x:=by unfold sY; rw [Ym0]
  have he : X x^2*(sU x^2*sH x)=(sP x*sY x)^2*sH x := by rw [← Xu]; ring
  rw [he,hh]; ring
lemma g_stable (x:ℝ): sg1 x=deriv g x := by
  unfold sg1; rw [(dg x).deriv,lp_st]
  unfold gd; rw [h_f,YDst]
  have he : X x*Xd x*(sU x^2*sH x)=(sP x*sY x)*sW x*sH x := by rw [← Xu,← X1u]; ring
  rw [he]; unfold sY; rw [Ym0]; ring
lemma c_stable (x:ℝ): sC x=Cp x := by
  rw [sC,d_stable,g_stable,k_stable,Cp,(ddg x).deriv,Kp]; ring
lemma sY_ident (x) : sY x* MillsC (-x)=1 := by
  unfold sY; rw [Ym0]; unfold Y MillsC
  rw [neg_phi,neg_p]; have h:=(q_pos x).ne'; field_simp [(phi_pos x).ne']
lemma sJneg (x): MillsJ (-x) = sB x/sY x := by
  have hh:=sY_ident x
  rw [B_st,eq_div_iff (show sY x≠0 from (Ymp _ _).ne')]
  unfold MillsJ; linarith
lemma rv_stable (x:ℝ): sRv x=deriv v x-x := by
  rw [sRv,sPe,v_deriv,← sJneg]; unfold MillsJ MillsC; ring
lemma v2_stable (x:ℝ): sV2 x=deriv (deriv v) x:= by
  have he : MillsC (-x) =1/sY x := by
    rw [eq_div_iff (show sY x≠0 from (Ymp _ _).ne'),mul_comm]; apply sY_ident
  rw [(ddv x).deriv,MillsW,MillsW,sJneg,he]
  unfold sV2 MillsJ MillsC; rw [sPe]; dsimp only; ring

def xs (t:ℝ):=sb*Real.sinh t
def ast (t:ℝ):=sb*Real.cosh t
def liftF (f:ℝ→ℝ) (t:ℝ):=f (xs t)
lemma hsb : 0<sb := by norm_num [sb]
lemma xD (t:ℝ): HasDerivAt xs (ast t) t := (Real.hasDerivAt_sinh t).const_mul sb
lemma aD (t:ℝ): HasDerivAt ast (xs t) t := (Real.hasDerivAt_cosh t).const_mul sb
lemma ap (t):0<ast t:= mul_pos hsb (Real.cosh_pos _)
lemma x_mono : StrictMono xs := strictMono_of_deriv_pos fun x=>by rw [(xD x).deriv]; apply ap
lemma x_ang (t): angle (xs t)=omegaP*t := by
  unfold angle xs; rw [mul_comm sb,mul_div_cancel_right₀ _ hsb.ne',Real.arsinh_sinh]
lemma ontoX (x:ℝ): ∃ t:ℝ,xs t=x := by
  refine ⟨Real.arsinh (x/sb),?_⟩
  unfold xs; rw [Real.sinh_arsinh,mul_div_cancel₀ _ hsb.ne']
end GeneralMahler.SCal

end

end OAI

import OAI.Geometry.Convex.GeneralMahler.MillsLog

namespace OAI
/-! §01 the primary profiles and their identities. -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology NNReal ENNReal
namespace GeneralMahler.Profile
open Layers

def X (x:ℝ) := p x/phi x
def Y (x:ℝ) := (1-p x)/phi x
def f (x:ℝ) := -(1-p x)-Real.log (p x)
def j (x:ℝ) := -p x-Real.log (1-p x)
def Xd (x:ℝ) := 1+x*X x
def Yd (x:ℝ) := x*Y x-1
def g (x:ℝ) := (1-X x^2*f x-Y x^2*j x)/2
def d (x:ℝ) := Xd x^2*f x+Yd x^2*j x
def v (x:ℝ) := Real.log (X x*Y x)
def N (g:ℝ→ℝ) := fun x:ℝ=> x*deriv g x - deriv (deriv g) x
def N2 (g:ℝ→ℝ) := fun x=>N g x+2*g x
lemma q_pos (x:ℝ) : 0<1-p x := sub_pos.mpr (p_lt_one x)
lemma xp (x:ℝ) : 0<X x := div_pos (p_pos x) (phi_pos x)
lemma yp (x:ℝ) : 0<Y x := div_pos (q_pos x) (phi_pos x)
lemma Y_ref (x:ℝ) : Y (-x)=X x := by simp [Y,neg_p,neg_phi,X]
lemma j_ref (x:ℝ) : j (-x)=f x := by simp [j,f,neg_p]
lemma dX (x:ℝ) : HasDerivAt X (Xd x) x := by
  convert (d_p x).div (d_phi x) (phi_pos x).ne' using 1
  all_goals first | rfl | (unfold Xd X; field_simp [ne_of_gt (phi_pos x)]; ring)
lemma dY (x:ℝ) : HasDerivAt Y (Yd x) x := by
  convert ((hasDerivAt_const x 1).sub (d_p x)).div (d_phi x) (phi_pos x).ne' using 1
  all_goals first | rfl | (simp only [Pi.sub_apply]; unfold Yd Y; field_simp [ne_of_gt (phi_pos x)]; ring)

def fd (x:ℝ) := -(phi x)*(1-p x)/p x
def jd (x:ℝ) := phi x * p x/(1-p x)
lemma df (x:ℝ) : HasDerivAt f (fd x) x := by
  convert (((hasDerivAt_const x 1).sub (d_p x)).neg.sub ((d_p x).log (p_pos x).ne')) using 1
  all_goals first | rfl | (unfold fd; field_simp [ne_of_gt (p_pos x)]; ring)
lemma dj (x:ℝ) : HasDerivAt j (jd x) x := by
  convert ((d_p x).neg.sub (((hasDerivAt_const x 1).sub (d_p x)).log (q_pos x).ne')) using 1
  all_goals first | rfl | (simp only [Pi.sub_apply]; unfold jd; field_simp [ne_of_gt (q_pos x)]; ring)

def gd (x:ℝ) := -(X x*Xd x*f x+Y x*Yd x*j x)

lemma v_log (x:ℝ) : v x= -LC x-LC (-x) := by
  have he : X x=(MillsC x)⁻¹ := by unfold X MillsC; rw [inv_div]
  have hh : Y x=(MillsC (-x))⁻¹ := by unfold Y MillsC; rw [neg_p,neg_phi,inv_div]
  rw [v,Real.log_mul (xp x).ne' (yp x).ne',he,hh,LC,LC,Real.log_inv,Real.log_inv]; ring
lemma dV (x:ℝ) : HasDerivAt v (MillsJ x-MillsJ (-x)) x := by
  rw [funext v_log]
  convert ((d_lc x).neg.sub ((d_lc (-x)).comp x (hasDerivAt_neg' x))) using 1
  all_goals first | rfl | ring
lemma v_deriv (x:ℝ) : deriv v x=MillsJ x-MillsJ (-x) := (dV x).deriv

lemma C_ids (x:ℝ) :
    X x^2*fd x + Y x^2*jd x = 0 ∧
    X x*Xd x*fd x + Y x*Yd x*jd x = -1 ∧
    Xd x^2*fd x + Yd x^2*jd x = -deriv v x := by
  rw [v_deriv]
  have h₁ := (p_pos x).ne'
  have h₂ := (q_pos x).ne'
  have h₃ := (phi_pos x).ne'
  simp only [Xd,Yd,X,Y,fd,jd,MillsJ,MillsC,neg_p,neg_phi]
  refine ⟨?_,?_,?_⟩ <;> field_simp <;> ring

lemma dg (x:ℝ) : HasDerivAt g (gd x) x := by
  have he := (((hasDerivAt_const x 1).sub (((dX x).pow 2).mul (df x))).sub
    (((dY x).pow 2).mul (dj x))).div_const 2
  convert he using 1
  all_goals first | rfl | (unfold gd; have hi := (C_ids x).1; norm_num; nlinarith)

lemma ddX (x:ℝ) : HasDerivAt Xd (X x+x*Xd x) x := by
  convert (((hasDerivAt_id' x).mul (dX x)).const_add 1) using 1
  all_goals first | rfl | ring
lemma ddY (x:ℝ) : HasDerivAt Yd (Y x+x*Yd x) x := by
  convert (((hasDerivAt_id' x).mul (dY x)).sub_const 1) using 1
  all_goals first | rfl | ring
lemma ddg (x:ℝ) :
    HasDerivAt (deriv g) (x*deriv g x+2*g x-d x) x := by
  rw [funext fun x=>(dg x).deriv]
  convert (((((dX x).mul (ddX x)).mul (df x)).add ((((dY x).mul (ddY x)).mul (dj x)))).neg)
    using 1
  all_goals first | rfl | (unfold gd g d; have hi := (C_ids x).2.1; simp only [Pi.mul_apply]; nlinarith)

lemma dd (x:ℝ) : HasDerivAt d (2*x*d x - deriv v x - 2*deriv g x) x := by
  have he := (((ddX x).pow 2).mul (df x)).add (((ddY x).pow 2).mul (dj x))
  convert he using 1
  all_goals first | rfl | skip
  rw [(dg x).deriv]
  unfold gd d Xd Yd
  have h := (C_ids x).2
  unfold Xd Yd at *
  obtain ⟨h,h'⟩ := h
  norm_num
  nlinarith

lemma ddv (x:ℝ) : HasDerivAt (deriv v) (2-MillsW x-MillsW (-x)) x := by
  simp_rw [funext v_deriv]
  convert ((d_mj x).sub ((d_mj (-x)).comp x (hasDerivAt_neg' x))) using 1
  all_goals first | rfl | ring
lemma d₃g (x:ℝ) :
    HasDerivAt (deriv (deriv g)) (3*deriv g x+x*deriv (deriv g) x-deriv d x) x := by
  rw [show deriv (deriv g) = fun x=>x*deriv g x+2*g x-d x from funext fun x=>(ddg x).deriv]
  convert ((((hasDerivAt_id' x).mul (ddg x)).add ((dg x).const_mul 2)).sub (dd x)) using 1
  simp_rw [(dd x).deriv,(dg x).deriv]; ring

lemma n_identity (x:ℝ) : N2 g x=d x := by rw [N2,N,(ddg x).deriv]; ring
lemma n_d_identity (x:ℝ) : N d x-deriv (deriv v) x= -N2 (fun t=>d t+deriv (deriv g) t) x := by
  have d' (x:ℝ) := ((dd x).differentiableAt.hasDerivAt)
  have v'' := (ddv x).differentiableAt.hasDerivAt
  have g'' (x:ℝ) := (ddg x).differentiableAt.hasDerivAt
  have h (x:ℝ) : deriv (fun t=>d t+deriv (deriv g) t) x =
      3*deriv g x+x*deriv (deriv g) x := by
    have h := ((d' x).fun_add (d₃g x)).deriv; rw [h]; ring
  have hx : deriv (deriv d) x=2*d x+2*x*deriv d x-deriv (deriv v) x-2*deriv (deriv g) x := by
    rw [funext (fun x=>(dd x).deriv)]
    have hi := (((((hasDerivAt_id' x).const_mul 2).mul (d' x)).sub v'').sub ((g'' x).const_mul 2)).deriv
    convert hi using 1
    all_goals first | rfl | (rw [(dd x).deriv] at *; ring)
  unfold N2 N
  rw [funext h,hx]
  have hi := (((g'' x).const_mul 3).fun_add ((hasDerivAt_id' x).mul (d₃g x))).deriv
  change x*deriv d x-_ -_ = -(x*_ - deriv (fun x=>3*deriv g x+x*deriv (deriv g) x) x+_)
  rw [show deriv (fun t=>3*deriv g t+t*deriv (deriv g) t) x=_ from hi]
  ring
end GeneralMahler.Profile

end

end OAI

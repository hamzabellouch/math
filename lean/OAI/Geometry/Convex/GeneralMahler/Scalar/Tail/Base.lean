import OAI.Geometry.Convex.GeneralMahler.Scalar.Grid

namespace OAI
/-! Tail jets use log coordinate t, denoted y here. This implements D=x∂_x. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal.Tail
open Profile Layers Jet
def XX:=Real.exp
def iv (y:ℝ):=(XX y)⁻¹
def ev (y:ℝ):=(iv y)^2 -- ξ
def Mk (n:Nat) (y:ℝ):=(XX y)^(n+1)*Ymk n (XX y)
def Qp (n:Nat) (y:ℝ):= (XX y)^n*phi (XX y)
def Z0:=Real.log (√(2*π))-1/2
def Lv (y:ℝ):=y+Z0
def Wv (y:ℝ):=ev y*Lv y
lemma xP (y):0<XX y:=Real.exp_pos _
lemma vP (y):0 < iv y:= inv_pos.mpr (xP y)
lemma iP (y):0 < ev y:= sq_pos_of_pos (vP y)
lemma Xd0 (y): HasDerivAt XX (XX y) y:= Real.hasDerivAt_exp _
lemma vd0 (y): HasDerivAt iv (-iv y) y:= by
  have hp:=xP y
  convert (Xd0 y).inv hp.ne' using 1
  all_goals first|rfl|(unfold iv; field_simp)
lemma id0 (y): HasDerivAt ev (-2*ev y) y:= by
  convert (vd0 y).pow 2 using 1
  all_goals first|rfl|(unfold ev; norm_num;ring)
lemma MkP (n:Nat) (y):0 < Mk n y:=mul_pos (pow_pos (xP y) _) (Ymp ..)
lemma M0e (y): Mk 0 y=1-ev y* Mk 1 y:= by
  unfold Mk ev iv; have hp:=xP y
  have he: (XX y)⁻¹^2*((XX y)^(1+1)*Ymk 1 (XX y))=Ymk 1 (XX y):=by field_simp
  rw [he]; norm_num
  linarith [R0 (XX y)]
lemma Mke (i:Nat) (y):
    Mk (i+1) y+ev y*Mk (i+2) y=((i+1:Nat):ℝ)*Mk i y := by
  unfold Mk ev iv; have hp:=xP y; let x:= XX y
  have he:= SCal.Rn x i
  have hh : x⁻¹^2*(x^(i+2+1)*Ymk (i+2) x) = x^(i+1)*Ymk (i+2) x := by
    change 0<x at hp; simp only [pow_succ]; field_simp
  change x^(i+1+1)*Ymk _ x+_ = _; rw [hh,pow_succ _ (i+1)]
  change _+x^(i+1)*Ymk _ x= ((i+1:Nat):ℝ)*(x^(i+1)*Ymk i x)
  linear_combination x^(i+1)*he
lemma Mk_hi (i:Nat) (y): Mk i y ≤ i.factorial:=by
  induction i with
  | zero=>
    rw [M0e]; have hp:=iP y; have h:=MkP 1 y
    norm_num; nlinarith
  | succ i ih=>
    have he:=Mke i y
    have hp:=iP y; have h:=MkP (i+2) y
    rw [Nat.factorial_succ]
    push_cast at *; nlinarith [show (0:ℝ) ≤ i by positivity]

lemma Dmk (n:Nat) (y): HasDerivAt (Mk n) (ev y*Mk (n+2) y) y := by
  let x:= XX y
  have hi:= ((Xd0 y).pow (n+1)).fun_mul ((DYmk x n).comp y (Xd0 y))
  have hh : HasDerivAt (Mk n) (((n+1:Nat):ℝ)*Mk n y-Mk (n+1) y) y := by
    convert hi using 1
    all_goals first|rfl | skip
    unfold Mk x; simp only [Nat.add_sub_cancel,pow_succ,Function.comp_apply,Pi.pow_apply]
    ring
  convert hh using 1
  linarith [Mke n y]

lemma Dqp (n:Nat) (y): HasDerivAt (Qp n) ((n:ℝ)*Qp n y-Qp (n+2) y) y:= by
  have h:= ((Xd0 y).pow n).fun_mul ((d_phi (XX y)).comp y (Xd0 y))
  convert h using 1
  all_goals first| rfl|skip
  unfold Qp
  cases n <;> simp only [Nat.add_sub_cancel,pow_succ,Function.comp_apply] <;> norm_num <;> ring
lemma Wd0 (y):HasDerivAt Wv (-2*Wv y+ev y) y:= by
  convert (id0 y).mul ((hasDerivAt_id' y).add_const Z0) using 1
  all_goals first | rfl|(unfold Wv Lv; ring)

namespace JT
def IJ (y:ℝ): J ℝ:=fun n=> (-2:ℝ)^n*ev y
def Wrec (w i:J ℝ) : ℕ→ℝ
  | 0=> w 0
  | n+1=> -2*Wrec w i n + i n
def WW (y:ℝ):= Wrec (ray (Wv y)) (IJ y)
def Prec:ℕ→ℕ→ℝ→ℝ
  | 0,m,y=> Qp m y
  | n+1,m,y=> m*Prec n m y - Prec n (m+2) y
def TP (m:ℕ):RF:=fun y n=>Prec n m y
-- Z=ξ^i Mk
def Mrec:ℕ→ℕ→ℕ→ℝ→ℝ
  | 0,m,i,y=>(ev y)^i*Mk m y
  | n+1,m,i,y=> -2*i*Mrec n m i y + Mrec n (m+2) (i+1) y
def TM (m i:ℕ):RF:= fun y n=> Mrec n m i y

lemma Ti : TW univ IJ:= by
  intro n x _
  convert (id0 x).const_mul ((-2:ℝ)^n) using 1
  all_goals first|rfl|(unfold IJ;rw [pow_succ];ring)
lemma IJ0 (x):IJ x 0=ev x:=by unfold IJ; ring
lemma Tw: TW univ WW:=by
  intro n x _
  induction n with
  | zero=>
    convert Wd0 x using 1
    all_goals first|rfl| simp only [WW,Wrec,IJ0,ray]
  | succ n ih=>
    exact ((ih.const_mul (-2:ℝ)).fun_add (Ti n x (mem_univ _)))
lemma Tp (i): TW univ (TP i):= by
  intro n x _
  induction n generalizing i with
  | zero=>exact Dqp i x
  | succ n ih=>exact ((ih i).const_mul (i:ℝ)).fun_sub (ih (i+2))
lemma TM0 (x m): TM m 0 x 0=Mk m x:=by simp [TM,Mrec]
lemma Tm (m i): TW univ (TM m i):= by
  intro n x _
  induction n generalizing m i with
  | zero=>
    convert ((id0 x).pow i).mul (Dmk m x) using 1
    all_goals first|rfl|skip
    unfold TM; simp only [Mrec]
    cases i <;> simp only [Nat.add_sub_cancel,pow_succ,Pi.mul_apply] <;> norm_num
    ring
  | succ n ih=>
    exact (((ih m i).const_mul (-2*(i:ℝ))).fun_add (ih (m+2) (i+1)))
end JT
end GeneralMahler.SCal.Tail

end

end OAI

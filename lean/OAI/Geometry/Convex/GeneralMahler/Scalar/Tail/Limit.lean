import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.Base
import OAI.Geometry.Convex.GeneralMahler.Scalar.Pass

namespace OAI
/-! §07 log domain elementary envelope values. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open JT Grid Profile Tag Cert Cert.IV Jet Layers
noncomputable section
def y0:= Real.log 64
lemma ey0 : XX y0=64:=Real.exp_log (by norm_num)
lemma ro_lim :
    (4158/1000:ℝ)≤ y0 ∧ y0≤416/100 ∧ 4/10≤ Z0 ∧ Z0≤42/100 := by
  have h64 : (64:ℝ)∈ c 64 := mc 64
  have hi:= mlbox h64 6
  have hh:=(mrt (mmul mtwo mpi))
  have hp:= msub (mlbox hh 6) mhalf
  have h₁:=subB hi (B:=band 41580 41600) (by decide +kernel)
  have h₂:=subB hp (B:=band 4000 4200) (by decide +kernel)
  rw [mem_band] at h₁ h₂
  unfold Z0 y0; norm_num at *
  exact ⟨by linarith [h₁.1],by linarith [h₁.2],by linarith [h₂.1],by linarith [h₂.2]⟩

lemma vsmall {y:ℝ} (h:y0≤ y): 64 ≤ XX y ∧ iv y ≤1/64 ∧ ev y≤1/4096 := by
  have hh:=exp_le_exp.mpr h
  change XX y0 ≤ XX y at hh
  rw [ey0] at hh
  have hi:iv y≤1/64:=by
    unfold iv; rw [one_div]
    exact (inv_le_inv₀ (xP _) (by norm_num)).mpr hh
  have he:=vP y
  refine ⟨hh,hi,?_⟩
  unfold ev; nlinarith
lemma econ {y:ℝ} (h:y0≤y):
    45/10≤ Lv y ∧ Wv y ≤112/100000+ 1/100000 ∧
      ev y*(Lv y-3/2)≤ 76/100000 := by
  have he (x:ℝ) (hx:y0≤x):45/10≤ Lv x := by
    obtain ⟨hh,_,hj,_⟩:=ro_lim
    unfold Lv; linarith
  have hv (a:ℝ) (ha:a≤3/2) :
      Wv y-ev y*a ≤ Wv y0-ev y0*a := by
    let f:=fun y=> Wv y-ev y*a
    have hd (x) : HasDerivAt f ((-2*Wv x+ev x)-(-2*ev x)*a) x :=
      (Wd0 x).fun_sub ((id0 x).mul_const a)
    apply antitoneOn_of_deriv_nonpos (f:=f) (convex_Ici y0)
      (fun x _=> (hd x).continuousAt.continuousWithinAt)
      (fun x _=> (hd x).differentiableAt.differentiableWithinAt)
      _ (mem_Ici.mpr le_rfl) h h
    intro x hx
    rw [(hd _).deriv]
    have hh:=he x (interior_subset hx)
    have hi:=iP x
    unfold Wv; nlinarith
  have hi:=hv 0 (by norm_num)
  have hj:=hv (3/2) le_rfl
  have hk:=ro_lim
  have h0: ev y0=1/4096:=by unfold ev iv; rw [ey0]; norm_num
  refine ⟨he y h,?_,?_⟩
  · unfold Wv Lv at *; rw [h0] at hi; linarith [hk.2.1,hk.2.2.2]
  unfold Wv at *
  rw [h0] at hj; unfold Lv at *; linarith [hk.2.1,hk.2.2.2]

lemma Q_limit {y:ℝ} (h:y0≤y) (i:Nat) (hi:i≤10):
    0≤ Qp i y ∧ Qp i y ≤1/10^9 := by
  have hp (x:ℝ) (i:ℕ): 0 < Qp i x:=mul_pos (pow_pos (xP x) _) (phi_pos _)
  have he : Qp 10 y ≤ Qp 10 y0 := by
    apply antitoneOn_of_deriv_nonpos (f:=Qp 10) (convex_Ici y0)
      (fun x _=> (Dqp 10 x).continuousAt.continuousWithinAt)
      (fun x _=> (Dqp 10 x).differentiableAt.differentiableWithinAt)
      _ (mem_Ici.mpr le_rfl) h h
    intro x hx
    rw [(Dqp _ _).deriv]
    have hh : Qp (10+2) x=(XX x)^2 * Qp 10 x := by unfold Qp; ring
    rw [hh]; rw [sub_nonpos]; apply mul_le_mul_of_nonneg_right _ (hp x 10).le; norm_num; nlinarith [(vsmall (show y0≤ x from interior_subset hx)).1]
  refine ⟨(hp y i).le, le_trans ?_ (he.trans ?_)⟩
  · unfold Qp; apply mul_le_mul_of_nonneg_right _ (phi_pos _).le
    apply pow_le_pow_right₀ _ hi
    linarith [(vsmall h).1]
  unfold Qp; rw [ey0,phi_apply,show (-(64^2)/2:ℝ)= -2048 by norm_num, Real.exp_neg]
  have hv : (√(2*π))⁻¹ ≤ 1 := by
    have hp : 1 ≤ √(2*π) := by
      have h := Real.pi_gt_three
      rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
    rwa [inv_le_one₀ (by positivity)]
  have he : (2:ℝ)^100 ≤ Real.exp 2048 := by
    have H := Real.add_one_le_exp 1
    have hi : (2:ℝ)^100 ≤ (Real.exp 1)^100 := by gcongr; linarith
    apply hi.trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr; norm_num
  have hs : (Real.exp 2048)⁻¹ ≤ ((2:ℝ)^100)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr he
  apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hv hs (by positivity) (by norm_num)) (by norm_num))
  norm_num
end

-- base envelope Boxes
def xiMax:IV:=(1:IV)/IV.c 4096
def XI : IV:= IV.span 0 xiMax
def BI : J IV:= fun n=> (-(2:IV))^n * XI
def wb:IV:= IV.span 0 (IV.c 113/IV.c 100000)
def wr : J IV
  | 0=> wb
  | n+1=> -(2:IV)*wr n+BI n
def pf0 : IV:= IV.span 0 (1/IV.c 1000000000)
def pr : ℕ→ℕ→IV
  | 0,i=> if i ≤ 10 then pf0 else unk
  | n+1,i=> (ub i)*pr n i-pr n (i+2)

def m0B (m:Nat):IV:=
  if m=0 then IV.span ((1:IV)-xiMax) 1
  else if m=1 then IV.span ((1:IV)- (IV.c 3)*xiMax) 1
  else IV.span 0 (ub m.factorial)
def mr:ℕ→ℕ→ℕ→IV
  | 0,m,i=>XI^i*m0B m
  | n+1,m,i=> -(2:IV)*ub i*mr n m i + mr n (m+2) (i+1)

variable {x:ℝ} (hv:y0≤ x)
include hv
lemma lXI: ev x∈ XI :=
  span_conv mz (mdiv mo (show (4096:ℝ)∈ c 4096 from mc 4096)) (iP _).le (vsmall hv).2.2
lemma lBI: Fits (IJ x) BI := fun _=> mmul (mpow (mneg mtwo) _) (lXI hv)
lemma lwb : Wv x∈ wb := by
  have he:= econ hv
  unfold wb
  apply span_conv mz (mdiv (mc 113) (mc 100000))
  · unfold Wv; nlinarith [he.1,iP x]
  norm_num; linarith [he.2.1]
lemma lwr: Fits (WW x) wr := by
  intro n; induction n with
  | zero=>exact lwb hv
  | succ n ih=> exact madd (mmul (mneg mtwo) ih) (lBI hv n)
lemma lpF (m:Nat): Fits (TP m x) fun n=> pr n m := by
  intro n; induction n generalizing m with
  | zero=>
    change _∈ pr 0 m; rw [pr]; split
    next h=>
      have hh:=Q_limit hv m h
      have ha : (1/10^9:ℝ) ∈ (1/IV.c 1000000000) := by
        convert mdiv mo (mc 1000000000) using 1; norm_num
      exact span_conv mz ha hh.1 hh.2
    trivial
  | succ n ih=> exact msub (mmul (ubb m) (ih m)) (ih _)
lemma lTm0 (m:Nat): Mk m x∈m0B m := by
  have h:= (vsmall hv).2.2
  have hQ:1/4096 ∈xiMax := mdiv mo (show (4096:ℝ) ∈ c 4096 from mc 4096)
  have h0:Mk 0 x ≤ 1 := by simpa using Mk_hi 0 x
  have h1:Mk 1 x ≤ 1 := by simpa using Mk_hi 1 x
  have hL : 1- 1/4096 ≤ Mk 0 x:= by rw [M0e]; nlinarith [iP x]
  unfold m0B
  split
  next hh=> subst m; exact span_conv (msub mo hQ) mo hL h0
  split
  next hh=>
    subst m
    refine span_conv (msub mo (mmul (mc 3) hQ)) mo ?_ h1
    have hh:= Mke 0 x
    have hi: Mk 2 x ≤ 2:=by convert Mk_hi 2 x; norm_num [Nat.factorial]
    norm_num at *; nlinarith [iP x]
  exact span_conv mz (ubb _) (MkP m x).le (Mk_hi m x)
lemma lTm (m i:Nat): Fits (TM m i x) (fun n=>mr n m i):= by
  intro n; induction n generalizing m i with
  | zero=>exact mmul (mpow (lXI hv) _) (lTm0 hv m)
  | succ n ih=>exact madd (mmul (mmul (mneg mtwo) (ubb _)) (ih m i)) (ih _ _)
end GeneralMahler.SCal.Tail

end OAI

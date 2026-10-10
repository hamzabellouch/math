import OAI.Geometry.Convex.GeneralMahler.Middle.Features

namespace OAI
/-! A posteriori approximation of functional via actual f bounded derivatives. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Profile Jet Segment SE
lemma cap_le (p:Ft): p.cap.b+p.cap.c≤ 6:= by cases p<;>
  norm_num [Ft.cap,Ft.cP,Ft.cC,Ft.cK,Ft.cJ,Cap.times]
lemma Ast_in : MonotoneOn ast (Ici 0):=by
  intro x hx y hy h
  unfold ast; apply mul_le_mul_of_nonneg_left _ hsb.le; rw [Real.cosh_le_cosh,
    abs_of_nonneg hx,abs_of_nonneg hy]; exact h
def stepG:ℝ:=1/200
lemma ndS (n:Nat):nd (n+1)=nd n+stepG:=by unfold nd stepG;push_cast;ring
-- cosh ratio ≤ e^δ
open Cert Cert.IV
lemma ratio01 (n:Nat): ast (nd (n+1)) ≤ ast (nd n)*(11/10):=by
  let x:=nd n
  have hs:0<stepG:=by unfold stepG;norm_num
  have he:exp stepG ≤11/10 := by
    have hp: stepG∈bd 50 := by convert mbd 50; norm_num [stepG]
    have hi:= mle (mebox 0 hp) (mbd 11000) (by decide +kernel)
    convert hi using 1; norm_num
  rw [ndS]
  change sb*cosh (x+stepG)≤_
  have hp:sinh x≤ cosh x:=by nlinarith [cosh_pos x,Real.cosh_sq_sub_sinh_sq x]
  have hc: cosh stepG+sinh stepG= exp stepG:=by rw [Real.sinh_eq,Real.cosh_eq]; ring
  have hi:cosh (x+stepG) ≤cosh x*exp stepG:=by
    rw [← hc,Real.cosh_add,mul_add]; nlinarith [Real.sinh_pos_iff.mpr hs]
  change sb* _ ≤ sb*cosh x*(11/10)
  rw [mul_assoc];exact mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left he (cosh_pos _).le)) hsb.le
lemma len_cmp(n):zn (n+1)-zn n ≤ (ast (nd n)* (11/10))*stepG:=by
  have hl := nd_m (show n<n+1 by omega)
  obtain ⟨t,ht,ha⟩:= exists_deriv_eq_slope xs hl
    ((show Continuous xs by unfold xs; fun_prop).continuousOn)
    (fun t _=> (xD t).differentiableAt.differentiableWithinAt)
  rw [(xD _).deriv,eq_div_iff (sub_pos.mpr hl).ne', show nd (n+1)-nd n=stepG from by rw [ndS];ring] at ha
  unfold zn;rw [← ha]
  have hq:0 ≤t:= le_trans (n_nn n) ht.1.le
  apply mul_le_mul_of_nonneg_right _ (by unfold stepG;norm_num)
  exact (Ast_in hq (n_nn _) ht.2.le).trans (ratio01 ..)

def perE:ℝ:=1/40000
lemma chordFeat (h:NG)(p:Ft)(n:ℕ)(t:ℝ)(hi:t∈Icc (0:ℝ) 1):
    |p.f (mix (zn n) (zn (n+1)) t)-mix (p.f (zn n)) (p.f (zn (n+1))) t| ≤ perE:=by
  have hp:=p.test h
  have hl:= (zNm (show n<n+1 by omega)).le
  let a:= ast (nd n)
  have ha:0 < a:= ap _
  have he (x:ℝ)(hx:x∈Icc (zn n) (zn (n+1))) :
      |deriv (deriv p.f) x|≤6/a^2:=by
    obtain ⟨b,hb⟩:=ontoX x
    have h₁:nd n ≤ b:= x_mono.le_iff_le.mp (hb.symm ▸ hx.1)
    have hut: a^2≤ ast b^2:=by
      unfold a;gcongr; apply Ast_in (n_nn n) ((n_nn n).trans h₁) h₁
    have hi:|NNf p.f b|≤6:=by
      have he:= p.guarded h
      have h₂:= he.fb b;have h₃:=he.fc b
      have ht: |thR b|≤1:=by nlinarith [sq_abs (thR b),(ri0 b).2]
      change |DotF p.f b| ≤ _ at h₂;change |DDot p.f b| ≤ _ at h₃
      unfold NNf
      have hi:= Guard.absMul ht h₂
      apply le_trans _ (cap_le p)
      rw [sub_eq_add_neg];
      convert (Guard.absAdd h₃ (show |-(thR b*DotF p.f b)|≤p.cap.b by rw [abs_neg]; simpa using hi)) using 1
      all_goals first|rfl|ring
    rw [le_div_iff₀ (sq_pos_of_pos ha),mul_comm]
    rw [(SCov _ hp _).1,hb,abs_mul,abs_of_nonneg (sq_nonneg _)] at hi
    exact le_trans (mul_le_mul_of_nonneg_right hut (_root_.abs_nonneg _)) hi
  have hh : 0≤6/a^2:=by positivity
  apply (chord_error (f:=p.f) (g:=deriv p.f) (h:=deriv (deriv p.f)) (fun x=>(hp.diff x).hasDerivAt)
    (fun x=>(hp.der.diff x).hasDerivAt) hl hi _ hh he).trans
  calc
    _ ≤ (6/a^2)/8*((a*(11/10))*stepG)^2 := by
      have hx:=len_cmp n
      change _ ≤ a * _ *_ at hx
      gcongr
    _ ≤ perE := by unfold stepG perE; field_simp; nlinarith

def rectA (p:Ft) (n:Nat):=(zn (n+1)-zn n)*((p.f (zn n)+p.f (zn (n+1)))/2)
def areaP (p:Ft) (x:ℝ):=∫ t in (0:ℝ)..x,p.f t
lemma area_pair (h:NG)(p:Ft)(x y:ℝ): areaP p y-areaP p x=(y-x)*bav p.f (x,y):=by
  have hf:= (p.test h).cont
  rw [bav_phys _ hf]
  have hi:= intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (μ:=volume) 0 x)
    (hf.intervalIntegrable x y)
  unfold areaP;linarith
lemma arealine (h:NG)(p:Ft)(n:Nat):
    |areaP p (zn (n+1))-areaP p (zn n)-rectA p n|≤
      (zn (n+1)-zn n)*perE:=by
  let x:=zn n;let y:=zn (n+1)
  have hf:= (p.test h).cont
  let f:=fun t:ℝ=>p.f (mix x y t)
  let g:=fun t:ℝ=>mix (p.f x) (p.f y) t
  have hc:Continuous f:= hf.comp (by unfold mix;fun_prop)
  have hd:Continuous g:=by unfold g mix;fun_prop
  have hI: ∀ x∈Ι (0:ℝ) 1,‖f x-g x‖≤ perE:= fun t ht=>by
    rw [uIoc_of_le zero_le_one] at ht
    exact chordFeat h p n t ⟨ht.1.le,ht.2⟩
  have hV:=intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun t=>f t-g t) hI
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable ..) (hd.intervalIntegrable ..),
    Real.norm_eq_abs] at hV
  have hh: (∫ t in (0:ℝ)..1,g t)=(p.f x+p.f y)/2:=by
    unfold g mix
    rw [intervalIntegral.integral_add,intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub,intervalIntegral.integral_const,integral_id]
    · simp; ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  rw [hh] at hV
  rw [area_pair h]; unfold rectA
  change |(y-x)*bav p.f _ - (y-x)*_| ≤ _
  have hu:x≤y:=(zNm (show n<n+1 by omega)).le
  rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hu)]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hu)
  change |(∫ t in (0:ℝ)..1,f t)-_|≤ _
  simpa only [sub_zero,abs_one,mul_one] using hV

def accum (p:Ft) : ℕ →ℝ
  | 0=>0
  | n+1=>accum p n+rectA p n
lemma sum_pair (h:NG)(p:Ft)(n m:Nat)(he:n ≤ m):
    |areaP p (zn m)-areaP p (zn n)-(accum p m-accum p n)| ≤ (zn m-zn n)*perE:=by
  induction m, he using Nat.le_induction with
  | base=> simp
  | succ m hm ih=>
    rw [accum]
    have hi:=Guard.absAdd ih (arealine h p m)
    convert hi using 2 <;> ring
end GeneralMahler.SCal.Mid

end

end OAI

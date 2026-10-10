import OAI.Geometry.Convex.GeneralMahler.Middle.Bound2
import OAI.Geometry.Convex.GeneralMahler.Segment.Phase

namespace OAI
/-! Center profiles for direct evaluation in compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE
inductive Ft
  | K|C|Q|J|V|M
deriving DecidableEq

instance : Fintype Ft :=
  Fintype.ofList [Ft.K, Ft.C, Ft.Q, Ft.J, Ft.V, Ft.M]
    (by intro p; cases p <;> simp)

noncomputable section
def k0:ℝ:=1/100
def c0:ℝ:=-(42/100)
def q0:ℝ:=16/100
namespace Ft
def f: Ft→ℝ→ℝ
  | K=> fun x=> Kp x-k0
  | C=> fun x=> Cp x-c0
  | Q=> fun x=> qu x-q0
  | M=> fun x=> (qu x-q0)^2
  | J=>uc
  | V=>us
def g(p:Ft):= liftF p.f
def cK:Cap:= ⟨18/1000,66/1000,26/100⟩
def cC:Cap:=⟨81/1000,247/1000,95/100⟩
def cP:Cap:=⟨96/1000,193/1000,56/100⟩
def cJ:Cap:=⟨22/100,1012/1000,466/100⟩
def cap:Ft→Cap
  | K=>cK
  | C=>cC
  | Q=>cP
  | M=> Cap.times cP cP
  | _=> cJ
lemma test (h:NG)(p:Ft):TestF p.f:= by
  have hf:=hSeg01 h
  cases p
  · exact testK.sub (TestF.const _)
  · exact testC.sub (TestF.const _)
  · exact hf.q_test.sub (TestF.const _)
  · exact hf.c_test
  · exact hf.s_test
  exact sq_test (hf.q_test.sub (TestF.const _))

lemma shiftGuard {f:ℝ→ℝ} (hf:TestF f) (c:ℝ) (A:Cap)
    (he:∀ x, |f (xs x)-c|≤A.a)
    (hb:∀ x, |DotF f x|≤A.b)
    (hc:∀ x, |DDot f x|≤A.c):
    Guard (fun x=>f (xs x)-c) A:= by
  have hv : Continuous (DDot f) := by
    have hh : DDot f= fun x=> xs x* deriv f (xs x) + ast x*(ast x*deriv (deriv f) (xs x)) :=
      funext fun x=> (dd_lift hf x).deriv
    have ha : Continuous xs:=by unfold xs; fun_prop
    have he:Continuous ast:=by unfold ast;fun_prop
    rw [hh]; exact (ha.mul (hf.der.cont.comp ha)).add (he.mul (he.mul (hf.der.der.cont.comp ha)))
  apply mkGuard (g:=DotF f) (h:=DDot f) _ _ hv he hb hc
  · intro x;exact (liftD hf x).sub_const c
  intro x; exact (dd_lift hf x).differentiableAt.hasDerivAt

lemma guardQ (h:NG):Guard (g Q) cP:=by
  apply shiftGuard (hqt h) q0 cP
  · intro x;unfold cP; dsimp; rw [abs_le]
    unfold q0; have he:=hQ h x;constructor<;>linarith [he.1,he.2]
  · intro x;unfold cP;dsimp;rw [abs_le];have he:=SE.hdQ h x; norm_num at *;exact he
  intro x;unfold cP;dsimp;rw [abs_le];have he:=hddQ h x; norm_num at *;exact he

lemma guardCS:Guard lc cJ∧ Guard ls cJ:=by
  let w:= Profile.omegaP
  let a:= fun x=> -w*ls x
  let b:=fun x=>w*lc x
  have hh:0≤w:=by norm_num [w,Profile.omegaP]
  have h: 0≤ Profile.r:=by norm_num [Profile.r]
  have h1(x): |lc x| ≤r ∧ |ls x|≤ r:=by
    rw [lc_e,ls_e,abs_mul,abs_mul,abs_of_nonneg h]
    exact ⟨mul_le_of_le_one_right h (abs_cos_le_one _),mul_le_of_le_one_right h (abs_sin_le_one _)⟩
  have h₁ :Continuous lc:=continuous_iff_continuousAt.mpr fun x=>(dlc x).continuousAt
  have h₂ :Continuous ls:=continuous_iff_continuousAt.mpr fun x=>(dls x).continuousAt
  have ha(x): |a x|≤ w*r ∧ |b x|≤ w*r:=by
    unfold a b; rw [abs_mul,abs_neg,abs_mul,abs_of_nonneg hh]; constructor<;>
      apply mul_le_mul_of_nonneg_left _ hh
    exact (h1 _).2;exact (h1 _).1
  have he:w*r=(1012/1000:ℝ):=by norm_num [w,omegaP,r]
  have hp:w*w*r ≤ (466/100:ℝ):=by norm_num [w,omegaP,r]
  have H1(x): HasDerivAt a (-w*b x) x:= (dls x).const_mul (-w)
  have H2(x): HasDerivAt b (w*a x) x:= (dlc x).const_mul w
  constructor
  · apply mkGuard dlc H1 (continuous_const.mul (continuous_const.mul h₁))
    · exact fun x=> (h1 _).1
    · intro x;change |a x|≤ 1012/1000;exact he ▸ (ha x).1
    intro x
    rw [abs_mul,abs_neg,abs_of_nonneg hh];change _ ≤ 466/100
    rw [mul_assoc] at hp
    exact le_trans (mul_le_mul_of_nonneg_left (ha x).2 hh) hp
  apply mkGuard dls H2 (continuous_const.mul (continuous_const.mul h₂))
  · exact fun x=>(h1 _).2
  · intro x; change |b x|≤1012/1000
    exact he ▸ (ha x).2
  intro x
  rw [abs_mul,abs_of_nonneg hh];change _ ≤466/100
  rw [mul_assoc] at hp
  exact le_trans (mul_le_mul_of_nonneg_left (ha x).1 hh) hp

lemma guarded (h:NG)(p:Ft):Guard p.g p.cap:=by
  cases p
  · apply shiftGuard testK k0 cK
    · intro x
      unfold k0;have he:=hK h x;rw [abs_le];change _∧_≤18/1000; dsimp [cK];constructor<;>linarith [he.1,he.2]
    · intro x;have he:=hdK h x; unfold cK;dsimp; rw [abs_le];norm_num at *;exact he
    intro x;have he:=hddK h x; unfold cK;dsimp;rw [abs_le];norm_num at *;exact he
  · apply shiftGuard testC c0 cC
    · intro x
      unfold c0; have he:=hC h x;rw [abs_le];dsimp [cC]; constructor<;>linarith [he.1,he.2]
    · intro x;have he:=hdC h x; unfold cC;dsimp; rw [abs_le];norm_num at *;exact he
    intro x;have he:=hddC h x; unfold cC;dsimp;rw [abs_le];norm_num at *;exact he
  · exact guardQ h
  · exact guardCS.1
  · exact guardCS.2
  exact (guardQ h).sq
end Ft
end
end GeneralMahler.SCal.Mid

end OAI

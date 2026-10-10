import OAI.Geometry.Convex.GeneralMahler.LinTest
import OAI.Geometry.Convex.GeneralMahler.LFun

namespace OAI
/-! Eq18 with fixed profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
def JVec (W:Mat m) := q.Jtest W uc+q.Jtest W us+q.Jtest W qu
def DVec := q.Dnorm uc+q.Dnorm us+q.Dnorm qu
def DelP (T:Mat m) := LDel q.FL 1 (ps d) + LDel q.FL T (fun x=>ps d x-v x)

lemma fc_pos (h:LayerOK) :
    0≤2*q.Ct (fun x=>x) (fl FF) -
      q.Ct (fl uc) (fl uc)-q.Ct (fl us) (fl us)-q.Ct (fl qu) (fl qu) := by
  let i := fun x:ℝ=> x
  let l := fun (f j:ℝ→ℝ) (u:Plane)=> q.ct u*(deriv f u.1*deriv j u.2)
  have he : 2*q.Ct i (fl FF)=(∫ u,l i (fl FF) u)+∫ u,l (fl FF) i u := by
    change _=q.Ct _ _+q.Ct _ _
    rw [show q.Ct (fl FF) i=q.Ct i (fl FF) from q.Cts]; ring
  rw [show 2*q.Ct _ _=_ from he]
  have hi {f g} (hf:TestF f) (hg:TestF g) := q.Ct_integrable hf hg
  have ha := fl_test h.c_test
  have hb := fl_test h.s_test
  have hc := fl_test h.q_test
  have hd := fl_test h.f_test
  change 0 ≤ _+_-(∫ u,l (fl uc) (fl uc) u)-(∫ u,l (fl us) (fl us) u)-∫ u,l (fl qu) (fl qu) u
  rw [← integral_add,← integral_sub,← integral_sub,← integral_sub]
  · apply integral_nonneg; intro x
    dsimp only [l,i]
    simp_rw [fl_d h.c_test,fl_d h.s_test,fl_d h.q_test,fl_d h.f_test,h.fN,
      deriv_id'',one_mul,mul_one]
    have hh := h.bh_contact x.1 x.2
    have h' := mul_nonneg (q.ct_pos x) hh.le
    change (0:ℝ) ≤ _
    linarith
  all_goals first | exact hi TestF.id hd | exact hi hd TestF.id | exact hi ha ha |
    exact hi hb hb | exact hi hc hc | exact (hi TestF.id hd).add (hi hd TestF.id) |
    exact ((hi TestF.id hd).add (hi hd TestF.id)).sub (hi ha ha) |
    exact (((hi TestF.id hd).add (hi hd TestF.id)).sub (hi ha ha)).sub (hi hb hb)

def Hpart (l:ℝ→ℝ) (u:Plane) := 2*(deriv (fl l) u.1*deriv (pl l) u.2)
def Hp0 (u:Plane) :=
  2*(deriv (fun x:ℝ=>x) u.1*deriv (pl FF) u.2) + deriv (fl FF) u.1*deriv (fun x=>x) u.2
lemma wt_deriv {f g} (hf:TestF f) (hg:TestF g) :
    Bwt fun u:Plane=>deriv f u.1*deriv g u.2 :=
  (Bwt.fst hf.der).mul (Bwt.snd hg.der)
lemma wt_Hp (h:LayerOK) : Bwt Hp0 :=
  ((Bwt.const 2).mul (wt_deriv TestF.id (pl_test h.f_test))).add (wt_deriv (fl_test h.f_test) TestF.id)
lemma wt_part {f} (hf:TestF f) : Bwt (Hpart f) :=
  (Bwt.const 2).mul (wt_deriv (fl_test hf) (pl_test hf))

lemma H_decomp (h:LayerOK) :
    HH=fun u=> Hp0 u-Hpart uc u-Hpart us u-Hpart qu u := by
  ext u; unfold Hpart Hp0
  simp_rw [fl_d h.f_test,fl_d h.c_test,fl_d h.s_test,fl_d h.q_test,h.fN,
    pl_d h.c_test,pl_d h.s_test,pl_d h.q_test,pl_d h.f_test,deriv_id'']
  unfold HH FF; ring
lemma H_ok (h:LayerOK) : Bwt HH := by
  rw [H_decomp h]
  exact (((wt_Hp h).sub (wt_part h.c_test)).sub (wt_part h.s_test)).sub
    (wt_part h.q_test)

lemma H_be (W:Mat m) (h:LayerOK) :
    q.LLw q.FL W HH=2*q.be q.FL W (fun x=>x) (pl FF)+q.be q.FL W (fl FF) (fun x=>x)-
      2*q.be q.FL W (fl uc) (pl uc)-2*q.be q.FL W (fl us) (pl us)-
      2*q.be q.FL W (fl qu) (pl qu) := by
  let o := q.LLw q.FL W
  have he (l:ℝ→ℝ) (hl:TestF l) :
      o (Hpart l)=2*q.be q.FL W (fl l) (pl l) := by
    unfold o Hpart
    rw [q.Lbar_scale, q.Le_id q.FL W (fl_test hl) (pl_test hl)]

  rw [H_decomp h,
    q.Lbar_sub q.FL W (((wt_Hp h).sub (wt_part h.c_test)).sub (wt_part h.s_test)) (wt_part h.q_test),
    q.Lbar_sub q.FL W ((wt_Hp h).sub (wt_part h.c_test)) (wt_part h.s_test),
    q.Lbar_sub q.FL W (wt_Hp h) (wt_part h.c_test),show q.LLw q.FL W (Hpart uc)=_ from he uc h.c_test,
    show q.LLw q.FL W (Hpart us)=_ from he us h.s_test,show q.LLw q.FL W (Hpart qu)=_ from he qu h.q_test]
  unfold Hp0
  rw [q.Lbar_add q.FL W ((Bwt.const _).mul (wt_deriv TestF.id (pl_test h.f_test)))
    (wt_deriv (fl_test h.f_test) TestF.id),q.Lbar_scale,
    q.Le_id q.FL W TestF.id (pl_test h.f_test),q.Le_id q.FL W (fl_test h.f_test) TestF.id]

lemma LLw_wt_sum (A B:Mat m) {f} (hf:Bwt f) :
    q.LLw q.FL (A+B) f = q.LLw q.FL A f+q.LLw q.FL B f := by
  unfold LLw
  have he (x z) : q.lk q.FL (A+B) f z x=q.lk q.FL A f z x+q.lk q.FL B f z x := by
    unfold lk Pj; rw [add_mul,trN_add]
  simp_rw [he,integral_add (q.lk_slice_i q.FL A hf _) (q.lk_slice_i q.FL B hf _)]
  rw [integral_add (q.Lbar_i q.FL A hf) (q.Lbar_i q.FL B hf)]

theorem entropy_decomp {T:Mat m} (he:1+T=q.covMat) (h:LayerOK) :
    q.delt d-etw T (q.Hmat v) ≤
      q.DelP T + q.sigma FF-q.DVec-q.JVec q.covMat-Pt T q.RR (q.FL.eval (deriv v))-
        q.LLw q.FL 1 HH -
        q.LLw q.FL T (fun u=> HH u+deriv (deriv v) u.2) := by
  let f := fun z=>uc z^2
  let j := fun z=>us z^2
  let k := fun z=>qu z^2
  let W := q.covMat
  have ha : TestF f := sq_test h.c_test
  have hb : TestF j := sq_test h.s_test
  have hc : TestF k := sq_test h.q_test
  have hh : d=fun z=>FF z-f z-j z-k z := by
    funext z
    have hi := u_eq z (h.rp z).le
    unfold f j k; linarith
  have hu : q.delt d=q.delt FF-q.delt f-q.delt j-q.delt k := by
    conv_lhs=>rw [hh]
    rw [q.delt_sub ((h.f_test.sub ha).sub hb) hc,q.delt_sub (h.f_test.sub ha) hb,
      q.delt_sub h.f_test ha]
  have Lh : LDel q.FL W (ps d)=LDel q.FL W (ps FF) - LDel q.FL W (ps f)-
      LDel q.FL W (ps j)-LDel q.FL W (ps k) := by
    conv_lhs=>rw [hh]
    have i' := h.f_test
    have h1 := i'.sub ha
    have h2 := h1.sub hb
    rw [ps_sub h2 hc,Delta_sub q.FL W (ps_test h2) (ps_test hc),
      ps_sub h1 hb,Delta_sub q.FL W (ps_test h1) (ps_test hb),
      ps_sub i' ha, Delta_sub q.FL W (ps_test i') (ps_test ha)]
  have ht : LDel q.FL W (ps d)-LDel q.FL T v=q.DelP T := by
    unfold W
    unfold DelP; rw [Delta_sub q.FL T (ps_test d_test) v_test]
    unfold LDel; rw [← he, etw_add (delta_reg q.FL (ps_test d_test)).ig]
    ring
  have hi : q.LLw q.FL T (fun u:Plane=> deriv (deriv v) u.2)=
      q.be q.FL T (fun x=>x) (deriv v) := by
    simpa using q.Le_id q.FL T TestF.id v_test.der
  rw [q.etw16a q.FL T v_test,q.MB_id,
    q.Lbar_add q.FL T (H_ok h) (Bwt.snd v_test.der.der),hi]
  have HH := q.H_be W h
  have hew : q.LLw q.FL W Profile.HH= q.LLw q.FL 1 Profile.HH+q.LLw q.FL T Profile.HH := by
    unfold W; rw [← he,q.LLw_wt_sum _ _ (H_ok h)]
  have hf := q.form_lin h.f_test
  have hp := q.fc_pos h
  unfold JVec DVec
  change q.LLw q.FL _ _=_ at HH
  linarith [q.form_sq h.q_test,q.form_sq h.c_test,q.form_sq h.s_test]
end ProjField
end GeneralMahler

end

end OAI

import OAI.Geometry.Convex.GeneralMahler.Linear.SpectralIBP

namespace OAI
/-! Eq25 scalar-functional profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ} [NeZero m]
namespace Profile
variable {f h:ℝ→ℝ}
lemma testC : TestF Cp :=
  d_test.neg.add ((TestF.const _).mul g_test.der.der)
lemma testK : TestF Kp :=
  d_test.sub ((TestF.const _).mul g_test)
lemma KN : Kp=N g := by
  ext x; have h := n_identity x
  unfold Kp; unfold N2 at h; linarith
lemma Kzero : ga Kp=0 := by
  have he := Nr_ga g_test
  rw [KN]
  change ga (fun x=>g x+N g x)=ga g at he
  rw [ga_add g_test (N_test g_test)] at he
  linarith
lemma Dadd (hf:TestF f) (hh:TestF h):
    deriv (fun x=>f x+h x)=fun x=>deriv f x+deriv h x :=
  funext fun x=>(((hf.diff x).hasDerivAt).fun_add (hh.diff x).hasDerivAt).deriv
lemma Dmul (hf:TestF f) (c:ℝ) :
    deriv (fun x=>c*f x)=fun x=>c*deriv f x :=
  funext fun x=>((hf.diff x).hasDerivAt.const_mul c).deriv
lemma N2sum (hf:TestF f) (hh:TestF h):
    N2 (fun x=>f x+h x)=fun x=>N2 f x+N2 h x := by
  unfold N2 N; rw [Dadd hf hh,Dadd hf.der hh.der]; ext; ring
lemma N2scale (hf:TestF f) (c:ℝ) :
    N2 (fun x=>c*f x)=fun x=> c*N2 f x := by
  unfold N2 N; rw [Dmul hf c,Dmul hf.der c]; ext; ring

lemma ND (hf:TestF f) (x) : deriv (N f) x=
    deriv f x + x*deriv (deriv f) x-deriv (deriv (deriv f)) x := by
  have he := ((((hasDerivAt_id' x).fun_mul ((hf.der.diff x).hasDerivAt))).fun_sub
    (hf.der.der.diff x).hasDerivAt).deriv
  unfold N; rw [he]; ring
lemma ND2 (hf:TestF f) :
    deriv (deriv (N f)) = N2 (deriv (deriv f)) := by
  rw [funext (ND hf)]
  ext x
  have hi := ((((hf.der.diff x).hasDerivAt.fun_add ((hasDerivAt_id' x).fun_mul
    (hf.der.der.diff x).hasDerivAt))).fun_sub (hf.der.der.der.diff x).hasDerivAt).deriv
  rw [hi]; unfold N2 N; ring

lemma second_f (hf:TestF f) : deriv (deriv (ps f))=N f := by
  rw [funext (ps_d hf),drv_sub (fl_test hf) ((TestF.const _).mul (pl_test hf)),fl_d hf,
    Dmul (pl_test hf) _,pl_d hf]
  ext x; unfold N2; ring
lemma second_D : deriv (deriv (ps d))= N2 Kp := by
  have he : Kp=fun x=>d x+(-2)*g x := by ext x; unfold Kp; ring
  rw [second_f d_test,he,N2sum d_test ((TestF.const _).mul g_test),
    N2scale g_test (-2)]
  ext x; dsimp only []; rw [n_identity]; unfold N2; ring
lemma second_C : deriv (deriv (fun x=>ps d x-v x+ar*Kp x))=N2 Cp := by
  have he : Cp=fun x=> (-1)*(d x+deriv (deriv g) x)+ar*deriv (deriv g) x := by ext x; unfold Cp; ring
  have hj := ps_test d_test
  rw [Dadd (hj.sub v_test) ((TestF.const _).mul testK),
    Dadd (hj.sub v_test).der (((TestF.const _).mul testK).der),
    drv_sub hj v_test,drv_sub hj.der v_test.der,Dmul testK ar,Dmul testK.der ar,
    second_f d_test,KN,ND2 g_test]
  have h := d_test.add g_test.der.der
  rw [he,N2sum ((TestF.const _).mul h) ((TestF.const _).mul g_test.der.der),
    N2scale h (-1),N2scale g_test.der.der ar]
  ext x; dsimp only []; rw [n_d_identity]; ring

-- use any second primitive; tilt so first derivatives match
lemma exists_N (hf:TestF f) (hh:TestF h)
    (he:deriv (deriv f)=N2 h) :
    ∃ F:ℝ→ℝ, TestF F ∧ deriv (deriv F)=h ∧ deriv f=deriv (N F) := by
  let g:= pl (pl h)
  have hG := pl_test hh
  have hg : TestF g := pl_test hG
  let c:= deriv f 0-deriv (N g) 0
  let F:=fun x=>g x+c*x
  have hF : TestF F := hg.add ((TestF.const _).mul TestF.id)
  have di : deriv g=pl h := pl_d hG
  have dF : deriv F=fun x=>deriv g x+c := by
    unfold F; rw [Dadd hg ((TestF.const _).mul TestF.id),Dmul TestF.id c]; ext; simp
  have dG : deriv (deriv g)=h := by rw [di, pl_d hh]
  have dF2 : deriv (deriv F)=h := by rw [dF,Dadd hg.der (TestF.const _),dG]; simp
  have dz : deriv f 0=deriv (N F) 0 := by
    rw [ND hF,dF2,dF]; unfold c; rw [ND hg,dG]; ring
  have hei : deriv (deriv f)=deriv (deriv (N F)) := by rw [he,ND2 hF,dF2]
  refine ⟨F,hF,dF2,?_⟩
  ext x
  have hi {w:ℝ→ℝ} (hw:TestF w) :
      (∫ t in (0:ℝ)..x,deriv (deriv w) t)=deriv w x-deriv w 0 := by
    apply intervalIntegral.integral_deriv_eq_sub (fun t _=>hw.der.diff t) (hw.der.der.cont.intervalIntegrable ..)
  have hp := hi hf
  rw [hei,dz] at hp
  exact sub_left_inj.mp (hp.symm.trans (hi (N_test hF)))

end Profile
namespace ProjField
variable (q:ProjField m) (T:Mat m)
lemma rm_diff {f j:ℝ→ℝ} (hf:TestF f) (hj:TestF j) (he:deriv (deriv f)=N2 j) :
    LDel q.FL T f=Pj T (q.sumS-1) (q.expL j)+q.RM T j := by
  obtain ⟨b,hb,hbj,h⟩ := exists_N hf hj he
  rw [L_ext _ _ hf (N_test hb) h,q.eq24 T hb,hbj]
lemma DelP_form :
    q.DelP T=Pj 1 (q.sumS-1) (q.expL Kp)+q.RM 1 Kp +
      (Pj T (q.sumS-1) (q.expL Cp)+q.RM T Cp -ar*trN (T*q.expL Kp)) := by
  have h := ps_test d_test
  have hb := h.sub v_test
  unfold DelP
  rw [q.rm_diff 1 h testK second_D]
  have hi := q.rm_diff T (hb.add ((TestF.const _).mul testK)) testC second_C
  rw [tw_add T hb ((TestF.const _).mul testK),L_cmul q.FL T ar testK] at hi
  have hu := L_formula q.FL T testK
  rw [Kzero,mul_zero,add_zero,q.W_int T testK] at hu
  rw [← hu] at hi; unfold ar at *
  linarith
end ProjField
end GeneralMahler

end

end OAI

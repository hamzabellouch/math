import OAI.Geometry.Convex.GeneralMahler.Linear.Gram

namespace OAI
/-! §06 weighted Dirichlet inequality. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open LPt HMode Profile Layers Segment
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (W:Mat m)
def locJ (i:Fin m) (f:ℝ→ℝ) (x:Rn m) :=
  Pj W (q.M i) (q.DLMat (fun x=>f x^2) x i)-Pj W (q.DLMat f x i) (q.DLMat f x i)
lemma DLherm (i:Fin m) {f} (hf:TestF f):
    regular (fun x=>q.DLMat f x i) := q.LD_reg _ (pl_test hf)
lemma DJi (i:Fin m) {f} (hf:TestF f):
    Integrable (q.locJ W i f) (normal m) :=
  (int_Pj _ (reg_constM _) (q.DLherm _ (sq_test hf))).sub
    (int_Pj _ (q.DLherm i hf) (q.DLherm i hf))
lemma locJ_form {f} (hf:TestF f):
    q.Jtest W f=
      ∑ i:Fin m,(∫ x,q.locJ W i f x ∂normal m) := by
  have hh := sq_test hf
  unfold Jtest; rw [q.L_identity W (pl_test hh),pl_d hh]
  unfold dirF Pt locJ
  simp_rw [integral_sub (int_Pj _ (reg_constM _) (q.DLherm _ hh)) (int_Pj _
    (q.DLherm _ hf) (q.DLherm _ hf)),Finset.sum_sub_distrib]
lemma mDout (i:Fin m) (x) {f} (hf:TestF f):
    let u := q.FL.Fr x
    u.loc (q.DLMat f x i)=mout (u.loc (q.M i)) (q.FL.ev x) (bav f) := by
  intro u
  unfold DLMat mout
  ext j k
  have he := q.mder_frame i j k (pl_test hf) x
  rw [pl_d hf] at he
  rw [show u.loc _ j k=_ from he]; simp only [Matrix.of_apply,mul_comm]; rfl
lemma Rpt_eq (i:Fin m) (x) {f} (hf:TestF f):
    let u := q.FL.Fr x
    q.locR W i f x=RR0 (u.loc (q.M i)) (u.loc W) (q.FL.ev x) f := by
  intro u
  unfold locR RR0
  rw [← u.pjL, ← u.pjL W (q.M i*q.M i)]
  rw [u.loc_mul,show u.loc (q.DLMat _ _ _)=_ from q.mDout i x hf,
    show u.loc (q.FL.eval f x)=_ from q.FL.evfrm x f]
  rfl
lemma Jpt_eq (i:Fin m) (x) {f} (hf:TestF f):
    let u:= q.FL.Fr x
    q.locJ W i f x=JJ0 (u.loc (q.M i)) (u.loc W) (q.FL.ev x) f := by
  intro u
  unfold locJ JJ0
  rw [← u.pjL, ← u.pjL W (q.DLMat _ x i)]
  rw [show u.loc (q.DLMat _ _ _)=_ from q.mDout i x (sq_test hf),
    show u.loc (q.DLMat _ _ _)=_ from q.mDout i x hf]

lemma R_nu {f} (hf:TestF f) :
    q.RM 1 f=q.nu (rest f) := by
  have he (i x) :
      q.locR 1 i f x=q.nupt i x (rest f) := by
    rw [q.Rpt_eq 1 i x hf]
    rw [Frm.loc_one,LPt.RR0_I _ _ _ hf ((q.FL.Fr x).HL (q.M_sym _))]
    rfl
  unfold nu RM; simp_rw [he]
lemma J_nu {f} (hf:TestF f): q.Jtest 1 f=q.nu (vdis f) := by
  have he (i x) :
      q.locJ 1 i f x=q.nupt i x (vdis f) := by
    rw [q.Jpt_eq 1 i x hf]
    rw [Frm.loc_one,LPt.JJ0_I _ _ _ hf ((q.FL.Fr x).HL (q.M_sym _))]; rfl
  rw [q.locJ_form 1 hf]
  unfold nu; simp_rw [he]
lemma J_sum (T:Mat m) {f} (hf:TestF f):
    q.Jtest (W+T) f=q.Jtest W f+q.Jtest T f := by
  have he (i x) : q.locJ (W+T) i f x=q.locJ W i f x+q.locJ T i f x := by
    unfold locJ Pj; simp_rw [add_mul,trN_add]; ring
  simp_rw [q.locJ_form _ hf,he,integral_add (q.DJi W _ hf) (q.DJi T _ hf),
    Finset.sum_add_distrib]
lemma J_vec (h:LayerOK):
    q.JVec (1+W)=q.nu vsum + q.JVec W := by
  unfold JVec vsum
  rw [q.J_sum _ _ h.c_test,q.J_sum _ _ h.s_test,q.J_sum _ _ h.q_test,
    q.J_nu h.c_test,q.J_nu h.s_test,q.J_nu h.q_test,
    q.nu_add ((Wv h.c_test).add (Wv h.s_test)) (Wv h.q_test),
    q.nu_add (Wv h.c_test) (Wv h.s_test)]; ring

lemma S_W (i:Fin m) (ht:W.IsHermitian) :
    hsN (W*q.M i)=trN ((q.M i*q.M i)*(W*W)) := by
  unfold hsN
  rw [star_mul,show star W=W from ht,show star (q.M i)=_ from q.M_sym i,mul_assoc,trN_cyclic W]
  simp only [mul_assoc]
lemma S_pair (ht:W.IsHermitian) :
    (∑ i:Fin m,hsN (W*q.M i)) = trN (q.sumS*(W*W)) := by
  unfold sumS; simp_rw [q.S_W W _ ht,← trL_apply,Finset.sum_mul,_root_.map_sum]
lemma eq26pt (i:Fin m) (hh:LayerOK) (ht:W∈specBox m tmin tmax) (x:Rn m):
    q.locR W i Cp x-q.locJ W i uc x-q.locJ W i us x-q.locJ W i qu x ≤
      lam*hsN (W*q.M i)+(1/(4*lam))*q.nupt i x (fun u=>bstar u^2)+
        tmax*q.nupt i x dsum := by
  let U:=q.FL.Fr x
  rw [q.Rpt_eq W _ _ testC,q.Jpt_eq W _ _ hh.c_test,q.Jpt_eq W _ _ hh.s_test,
    q.Jpt_eq W _ _ hh.q_test,← hsN_loc _ U,U.loc_mul]
  apply LPt.pt26 _ _ _ (U.HL (q.M_sym i)) (U.HL ht.1) _ hh
  have hi := U.loc_le ht.2.2
  rwa [scalar,U.loc_smul,U.loc_one] at hi
lemma eq26sum (i:Fin m) (hh:LayerOK) (ht:W∈specBox m tmin tmax) :
    (∫ x,q.locR W i Cp x ∂normal m)-(∫ x,q.locJ W i uc x ∂normal m)-
      (∫ x,q.locJ W i us x ∂normal m)-(∫ x,q.locJ W i qu x ∂normal m) ≤
      lam*hsN (W*q.M i)+(1/(4*lam))*(∫ x,q.nupt i x (fun u=>bstar u^2) ∂normal m)+
        tmax*(∫ x,q.nupt i x dsum ∂normal m) := by
  have h := q.DRi W i testC
  have ha := q.DJi W i hh.c_test
  have hb := q.DJi W i hh.s_test
  have hc := q.DJi W i hh.q_test
  have hi := (q.nu_i (Wsq (Wb hh)) i).const_mul (1/(4*lam))
  have hj := (q.nu_i (Wd hh) i).const_mul tmax
  have H := integral_mono (Integrable.sub (((h.sub ha).sub hb)) hc)
    (((integrable_const _).add hi).add hj) (q.eq26pt W i hh ht)
  rw [integral_sub' ((h.sub ha).sub hb) hc,integral_sub' (h.sub ha) hb,integral_sub' h ha,
    integral_add' ((integrable_const _).add hi) hj,integral_add' (integrable_const _) hi] at H
  simpa only [integral_const_mul,integral_const,probReal_univ,one_smul] using H

lemma eq26 (hh:LayerOK) (ht:W∈specBox m tmin tmax) :
    q.RM W Cp-q.JVec W ≤
      lam*trN (q.sumS*(W*W))+(1/(4*lam))*q.nu (fun u=>bstar u^2)+
        tmax*q.nu dsum := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i (_:i∈Finset.univ)=>q.eq26sum W i hh ht)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at h
  rw [q.S_pair W ht.1] at h
  rw [RM,JVec,q.locJ_form W hh.c_test,q.locJ_form W hh.s_test,q.locJ_form W hh.q_test]
  unfold nu; linarith
end ProjField
end GeneralMahler

end

end OAI

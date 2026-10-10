import OAI.Geometry.Convex.GeneralMahler.Beta

namespace OAI
/-! Layer evaluation comparisons (16). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma pj_I (W A:Mat m) : Pj W A 1=trN (W*A) := by
  have hi : jprod A 1=A := by unfold jprod; simp only [mul_one,one_mul]; module
  unfold Pj; rw [hi]

namespace FieldMat
variable (B:FieldMat m)
omit [NeZero m] in
lemma eval_scale {f:ℝ→ℝ} (hf:TestF f) (a:ℝ) (x) :
    B.eval (fun z=>a*f z) x=a•B.eval f x := cfc_const_mul a f _ hf.cont.continuousOn
omit [NeZero m] in
lemma eval_mul {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (x) :
    B.eval (fun z=>f z*g z) x=B.eval f x*B.eval g x :=
  cfc_mul f g _ hf.cont.continuousOn hg.cont.continuousOn
omit [NeZero m] in
lemma eval_sub {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) (x) :
    B.eval (fun z=>f z-g z) x=B.eval f x-B.eval g x :=
  cfc_sub f g _ hf.cont.continuousOn hg.cont.continuousOn
omit [NeZero m] in
lemma eval_const (a:ℝ) (x) : B.eval (fun _=>a) x=scalar m a := by
  unfold eval; rw [scalar_eq,cfc_const a (B.A x) (show IsSelfAdjoint (B.A x) from B.sym x)]
omit [NeZero m] in
lemma ccomm (x) (f g) : Commute (B.eval f x) (B.eval g x) := cfc_commute_cfc ..
end FieldMat
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (W:Mat m)
def BDiff (f:ℝ→ℝ) (x:Rn m) := B.eval f x-scalar m (ga f)
def LDel (f:ℝ→ℝ) := etw W (BDiff B f)
omit [NeZero m] in
lemma mb_plus {f} (x:Rn m) : q.Hmat f x=q.MB B f x+BDiff B f x := by unfold MB BDiff; abel

omit [NeZero m] in
lemma delta_reg {f} (hf:TestF f): regular (BDiff B f) :=
  ⟨(B.eval_reg hf).p.sub (PolyBound.const _),
    (B.eval_reg hf).meas.sub aestronglyMeasurable_const⟩
lemma mb_reg {f} (hf:TestF f) : regular (q.MB B f) := by
  have h : q.MB B f=fun x=> q.Hmat f x-BDiff B f x := by
    funext x; unfold MB BDiff; abel
  rw [h]
  have hh := q.regH hf; have hg := delta_reg B hf
  exact ⟨hh.p.sub hg.p,hh.meas.sub hg.meas⟩

omit [NeZero m] in
lemma proj_int (W:Mat m) {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>PJ W (f x) (g x)) (normal m) := by
  simp_rw [pJ_eq]
  have h := (pj_cont W).comp_aestronglyMeasurable (hf.meas.prodMk hg.meas)
  exact (pj_p hf.p hg.p W).gaussian_integrable
    h
omit [NeZero m] in
lemma etwReg (W:Mat m) {f:Rn m→Mat m} (hf:regular f) :
    Integrable (fun x=>trN (W*f x)) (normal m) := int_etw W hf.ig

lemma mb_ibp (x:Rn m) {f j b:ℝ→ℝ} (hf:TestF f) (_hj:TestF j) (hb:TestF b)
    (hB:∀ x,deriv b x=deriv f x*j x) :
    PJ W (q.MB B f x) (B.eval j x)= trN (W*q.MB B b x) -
      (∫ z,q.betaK B W f j z x) := by
  let l := (PJ W).flip (B.eval j x)
  let k := (PJ W).flip (1:Mat m)
  have he (z:ℝ) : q.betaK B W f j z x= l (q.zE B f z x)- k (q.zE B b z x) := by
    have ht (a b:ℝ) (A C:Mat m) :
        Pj W (a•A) (C-b•(1:Mat m))=PJ W (a•A) C-PJ W ((a*b)•A) 1 := by
      have hj : Pj W (a•A) ((b:ℝ)•(1:Mat m))=PJ W ((a*b)•A) 1 := by
        rw [pJ_eq,pj_scale]
        have he := pj_scale (a*b) 1 W A 1
        simp only [one_smul,one_mul] at he
        rw [he]; ring
      rw [← hj]
      simp_rw [← pJ_eq,_root_.map_sub]
    unfold betaK l k FieldMat.eVal zE scalar
    rw [ht,hB]; rfl
  have he' (A:Mat m) : trN (W*A)= k A := by rw [← pj_I,← pJ_eq]; rfl
  rw [q.mb_eq B hf _,q.mb_eq B hb _]
  rw [he']
  change l (-(∫ z,q.zE B f z x)) = k _ - _
  simp_rw [he]
  have ha := q.zi B hf x; have hc := q.zi B hb x
  rw [integral_sub (l.integrable_comp ha) (k.integrable_comp hc),
    l.integral_comp_comm ha,k.integral_comp_comm hc, _root_.map_neg,_root_.map_neg]; ring

lemma mb_comp {f j b:ℝ→ℝ} (hf:TestF f) (hj:TestF j) (hb:TestF b)
    (hB:∀ x,deriv b x=deriv f x*j x) :
    Pt W (q.MB B f) (B.eval j)=etw W (q.MB B b) - q.be B W f j := by
  unfold Pt etw et be
  simp_rw [← pJ_eq,q.mb_ibp B W _ hf hj hb hB]
  have hi := q.bMS B W hf hj
  rw [integral_sub]
  · exact int_etw _ (q.mb_reg B hb).ig
  exact (mixed_integrable (ν:=normal m) (μ:=volume) hi.1 hi.2.aestronglyMeasurable).integral_prod_right
lemma etw_H {f} (hf:TestF f) :
    etw W (q.Hmat f)=etw W (q.MB B f)+LDel B W f := by
  unfold LDel etw et
  simp_rw [q.mb_plus B,mul_add,trN_add]
  exact integral_add (int_etw _ (q.mb_reg B hf).ig) (int_etw _ (delta_reg B hf).ig)
lemma etw16a {j} (hj:TestF j) :
    etw W (q.Hmat j)= LDel B W j+Pt W (q.MB B (fun x=>x)) (B.eval (deriv j))
      + q.be B W (fun x=>x) (deriv j) := by
  rw [q.mb_comp B W TestF.id hj.der hj (by intro x; simp),q.etw_H B W hj]; ring

omit [NeZero m] in
lemma Delta_sub {f j} (hf:TestF f) (hj:TestF j) :
    LDel B W (fun x=>f x-j x)=LDel B W f-LDel B W j := by
  unfold LDel etw et
  have he (x:Rn m) : BDiff B (fun x=>f x-j x) x= BDiff B f x-BDiff B j x := by
    unfold BDiff; rw [B.eval_sub hf hj,ga_sub hf hj]; unfold scalar; module
  simp_rw [he,mul_sub,trN_sub]
  exact integral_sub (etwReg _ (delta_reg B hf)) (etwReg _ (delta_reg B hj))

lemma f_pair16 {f j w:ℝ→ℝ} (hf:TestF f) (hj:TestF j)
    (he:ga f=0) (hw:TestF w) (h':∀ x,deriv w x=f x*deriv j x) :
    Pt q.covMat (q.Hmat f) (B.eval j) =
      (∫ x,q.layerW x*(f x*j x)) + (LDel B q.covMat w-∫ x,q.dm x*w x) -
        q.be B q.covMat f j := by
  let W := q.covMat
  let g := fun x=>f x*j x
  let b := fun x=>g x-w x
  have hg := hf.mul hj
  have hb := hg.sub hw
  have h (x:ℝ) : deriv b x=deriv f x*j x := by
    have he := ((((hf.diff x).hasDerivAt).fun_mul (hj.diff x).hasDerivAt).fun_sub
      (hw.diff x).hasDerivAt).deriv
    change deriv b x=_ at he; rw [he,h']; ring
  have hi := q.mb_comp B W hf hj hb h
  have hh : Pt W (q.Hmat f) (B.eval j) =
      Pt W (q.MB B f) (B.eval j) + etw W (B.eval g) := by
    unfold Pt etw et
    have he (x) : Pj W (q.Hmat f x) (B.eval j x)=
        Pj W (q.MB B f x) (B.eval j x)+trN (W*B.eval g x) := by
      rw [q.mb_plus B]
      unfold BDiff
      rw [he]; simp only [scalar,zero_smul,sub_zero]
      have he' : jprod (B.eval f x) (B.eval j x)=B.eval g x := by
        unfold jprod g; rw [B.eval_mul hf hj, (B.ccomm x j f).eq]; module
      calc
        _ = Pj W (q.MB B f x) (B.eval j x)+Pj W (B.eval f x) (B.eval j x) := by
          simp_rw [← pJ_eq]; rw [_root_.map_add,_root_.add_apply]
        _ = _ := by unfold Pj; rw [he']
    simp_rw [he]
    rw [integral_add]
    · simp_rw [← pJ_eq]; exact proj_int _ (q.mb_reg B hf) (B.eval_reg hj)
    exact int_etw _ (B.eval_reg hg).ig
  have h₁ : etw W (B.eval g)= LDel B W g+q.s0*ga g := by
    have he (x:Rn m) :
        trN (W*B.eval g x)=trN (W*BDiff B g x)+q.s0*ga g := by
      unfold BDiff s0 scalar W; rw [mul_sub,trN_sub,mul_smul_comm,mul_one,trN_smul]; ring
    unfold etw LDel etw et; simp_rw [he]
    rw [integral_add (int_etw W (delta_reg B hg).ig) (integrable_const _)]
    simp; rfl
  have h₂ := q.etw_H B W hb
  have h₃ := q.h_weighted hb
  change etw W (q.Hmat b)= _ at h₃
  have h₄ : (∫ x,q.dm x*b x)=(∫ x,q.layerW x*g x)-q.s0*ga g-(∫ x,q.dm x*w x) := by
    have he (x) : q.dm x*b x=q.layerW x*g x-q.s0*(phi x*g x)-q.dm x*w x := by
      unfold dm b; ring
    simp_rw [he]; have hi:= ga_i hg; have hh:= q.moment_w.int_test hg
    rw [integral_sub,integral_sub hh (hi.const_mul _),integral_const_mul]; rfl
    · exact hh.sub (hi.const_mul _)
    exact q.dm_m.int_test hw
  have h₅ := Delta_sub B W hg hw
  change Pt W _ _=(∫ x,q.layerW x*g x)+(LDel B W w-_)-_
  linarith
end ProjField
end GeneralMahler

end

end OAI

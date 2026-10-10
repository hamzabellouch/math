import OAI.Geometry.Convex.GeneralMahler.Budget.Eq23

namespace OAI
/-! §06 Gaussian spectral averaging functional. Eq24 in normalized trace pairing. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}
lemma reg_constM (W:Mat m): regular (fun _:Rn m=>W) :=
  ⟨PolyBound.const _,aestronglyMeasurable_const⟩
lemma int_Pj (W:Mat m) {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) :
    Integrable (fun x=>Pj W (f x) (g x)) (normal m) := by
  simp_rw [← pJ_eq]; apply ProjField.proj_int _ hf hg

namespace ProjField
variable [NeZero m] (q:ProjField m) (W:Mat m)
def sumS : Mat m := ∑ i:Fin m,q.M i*q.M i
def locR (l:Fin m) (f:ℝ→ℝ) (x:Rn m) :=
  Pj W (q.M l) (q.DLMat f x l) -
    Pj W (q.M l*q.M l) (q.FL.eval f x)
def RM (f:ℝ→ℝ) :=
  ∑ l:Fin m,∫ x,q.locR W l f x ∂normal m

lemma DRi (l:Fin m) {f:ℝ→ℝ} (hf:TestF f) :
    Integrable (q.locR W l f) (normal m) :=
  (int_Pj _ (reg_constM _) (q.LD_reg l (pl_test hf))).sub
    (int_Pj _ (reg_constM _) (q.FL.eval_reg hf))

lemma dl_again (i:Fin m) {f:ℝ→ℝ} (hf:TestF f) (x:Rn m) :
    q.DLMat (deriv f) x i=fderiv ℝ (q.FL.eval f) x (e i) := by
  unfold DLMat
  apply (q.FL.Fr x).loc_inj
  ext j k
  rw [q.mder_frame _ _ _ hf x,q.mder_frame _ _ _ (pl_test hf.der) x,pl_d hf.der]

lemma xf_reg (l:Fin m) (f:ℝ→ℝ) (hf:TestF f) :
    regular (fun x:Rn m=> x l • q.FL.eval f x) :=
  (q.FL.eval_reg hf).smul
    (show regular (coord l) from ⟨PolyBound.clm _,(coord l).continuous.aestronglyMeasurable⟩)
lemma dl_identity (i:Fin m) {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,q.DLMat (deriv f) x i ∂normal m)= ∫ x:Rn m,x i • q.FL.eval f x ∂normal m := by
  let g := q.FL.eval f
  let h := fun (x:Rn m)=> fderiv ℝ g x (e i)
  have hg : regular g := q.FL.eval_reg hf
  have he : Differentiable ℝ g := fun x=> (q.hasdl x hf).differentiableAt
  have hh : regular h := q.LD_reg i hf
  have ht := coef_raise hg.p (PLip.fd he (q.dPoly hf)) he.continuous
    (ae_of_all _ fun x=> (he x).hasFDerivAt) i hh.p hh.meas 0
  simp_rw [q.dl_again i hf]
  unfold cof at ht
  simpa only [Mzero, Mi1, one_smul, Pi.zero_apply,Nat.zero_add,sn,Nat.cast_one,Real.sqrt_one] using ht

lemma coord_pb (l:Fin m) {f:ℝ→ℝ} (hf:TestF f) :
    (∫ x,Pj W (q.M l) (q.DLMat (deriv f) x l) ∂normal m) =
      ∫ x:Rn m,Pj W (q.M l) (x l • q.FL.eval f x) ∂normal m := by
  simp_rw [← pJ_eq]
  let g := PJ W (q.M l)
  let D := fun x=>q.DLMat (deriv f) x l
  have hi : regular D := q.LD_reg l (pl_test hf.der)
  change (∫ x,g (D x) ∂normal m)= ∫ x:Rn m,g _ ∂normal m
  rw [g.integral_comp_comm hi.ig,g.integral_comp_comm (q.xf_reg l f hf).ig,
    show (∫ x, D x ∂normal m) =_ from q.dl_identity l hf]

-- the evaluation weighted by W
lemma L_identity {f:ℝ→ℝ} (hf:TestF f) :
    etw W (fun x:Rn m=> q.Lmat x*q.FL.eval f x) =
      ∑ i:Fin m, (∫ x,Pj W (q.M i) (q.DLMat (deriv f) x i) ∂normal m) := by
  have he (x:Rn m) : trN (W*(q.Lmat x*q.FL.eval f x)) =
      ∑ i:Fin m, Pj W (q.M i) (x i • q.FL.eval f x) := by
    let A := q.FL.eval f x
    have hh : jprod (q.Lmat x) A=q.Lmat x*A := by
      have hx := (q.FL.ccomm x f (fun z=>z)).eq
      rw [q.evId] at hx
      change A*q.Lmat x=_ at hx; unfold jprod
      rw [hx]; module
    rw [show trN (W*(q.Lmat x*q.FL.eval f x))=Pj W (q.Lmat x) A from
      (congrArg (fun z=>trN (W*z)) hh).symm]
    unfold Lmat; simp_rw [← pJ_eq]
    rw [_root_.map_sum,_root_.sum_apply]
    congr 1
    ext i
    rw [pJ_eq,pJ_eq,pJ_smul_left,pJ_smul_right]
  unfold etw et; simp_rw [he,q.coord_pb W _ hf]
  rw [integral_finsetSum]
  intro i _; exact int_Pj W (reg_constM _) (q.xf_reg i f hf)

lemma RM_Form {g:ℝ→ℝ} (hg:TestF g) :
    q.RM W (deriv g)= etw W (fun x=> q.Lmat x*q.FL.eval g x)-
      Pj W q.sumS (q.expL (deriv g)) := by
  unfold RM sumS
  simp_rw [q.L_identity W hg,locR, integral_sub (int_Pj _
    (reg_constM _) (show regular (fun x=>q.DLMat (deriv g) x _) from q.LD_reg _ (pl_test hg.der)))
    (int_Pj _ (reg_constM _) (q.FL.eval_reg hg.der))]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp_rw [← pJ_eq]
  rw [_root_.map_sum,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (PJ W _).integral_comp_comm (q.FL.eval_reg hg.der).ig

lemma W_int {f:ℝ→ℝ} (hf:TestF f) :
    etw W (q.FL.eval f)=trN (W*q.expL f) := by
  unfold etw et
  simp_rw [← pj_I, pj_sym, ← pJ_eq]
  exact (PJ W _).integral_comp_comm (q.FL.eval_reg hf).ig

lemma eq24 {f:ℝ→ℝ} (hf:TestF f) :
    LDel q.FL W (N f)=Pj W (q.sumS-1) (q.expL (deriv (deriv f))) +
      q.RM W (deriv (deriv f)) := by
  have hh : ga (N f)=0 := by
    have he := Nr_ga hf
    change ga (fun x=>f x+N f x)=ga f at he
    rw [ga_add hf (N_test hf)] at he
    linarith
  rw [show LDel q.FL W _= etw W (q.FL.eval (N f)) from by
    have hi := L_formula q.FL W (N_test hf)
    rw [hh,mul_zero,add_zero] at hi; exact hi.symm]
  have he : etw W (q.FL.eval (N f))=
      etw W (fun x=>q.Lmat x*q.FL.eval (deriv f) x) -
        trN (W*q.expL (deriv (deriv f))) := by
    rw [← q.W_int W hf.der.der]
    let h := fun x:ℝ=> x*deriv f x
    have H := TestF.id.mul hf.der
    have he (x) : q.FL.eval (N f) x=q.FL.eval h x-q.FL.eval (deriv (deriv f)) x :=
      q.FL.eval_sub H hf.der.der _
    have hx (x) : q.Lmat x*q.FL.eval (deriv f) x=q.FL.eval h x := by
      rw [show q.FL.eval h x=_ from q.FL.eval_mul TestF.id hf.der _,q.evId]
    unfold etw et; simp_rw [he,hx,mul_sub,trN_sub]
    exact integral_sub (etwReg _ (q.FL.eval_reg H)) (etwReg _ (q.FL.eval_reg hf.der.der))
  rw [he,q.RM_Form W hf.der]
  let A := q.expL (deriv (deriv f))
  have h : Pj W (q.sumS-1) A=Pj W q.sumS A-trN (W*A) := by
    simp_rw [← pj_I,pj_sym W A 1, ← pJ_eq,_root_.map_sub,_root_.sub_apply]
  rw [show Pj W (q.sumS-1) _=_ from h]
  unfold A; ring
end ProjField
end GeneralMahler

end

end OAI

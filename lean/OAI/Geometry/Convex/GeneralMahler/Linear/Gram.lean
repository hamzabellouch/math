import OAI.Geometry.Convex.GeneralMahler.Linear.Nu

namespace OAI
/-! §06 weighted Dirichlet inequality: in a spectral frame. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
namespace LPt
open HMode Profile Layers Segment
variable {m:ℕ}
variable (M W:Mat m) (l:Fin m→ℝ)
def uf (f:ℝ→ℝ) := Matrix.diagonal (fun i=> f (l i))
def RR0 (f:ℝ→ℝ) :=
  Pj W M (mout M l (bav f))-Pj W (M*M) (uf l f)
def JJ0 (f:ℝ→ℝ) :=
  Pj W M (mout M l (bav (fun x=>f x^2)))-
  Pj W (mout M l (bav f)) (mout M l (bav f))

lemma uf_sym (f:ℝ→ℝ) : (uf l f).IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr fun _=> rfl
lemma base_PJ {A B C:Mat m} (ha:A.IsHermitian) (hb:B.IsHermitian) (hc:C.IsHermitian) :
    Pj A B C=ipN (A*B) C := by
  rw [pj_cyc3 ha hb hc,trN_cyclic _ A]; unfold ipN; rw [mul_assoc,show star C=C from hc]

lemma RR0_eq (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) (hw:W.IsHermitian) :
    RR0 M W l f=ipN (W*M) (mout M l (rest f)) := by
  have h : mout M l (rest f)=mout M l (bav f)-uf l f*M := by
    ext i j; rw [Matrix.sub_apply]
    unfold uf rest mout; rw [Matrix.diagonal_mul]; simp only [Matrix.of_apply]; ring
  have hi : Pj W (M*M) (uf l f)=ipN (W*M) (uf l f*M) := by
    rw [base_PJ hw (sqPSD hm).posSemidef.1 (uf_sym ..)]
    unfold ipN; rw [star_mul,show star M=M from hm,mul_assoc]; simp only [mul_assoc]
  rw [RR0, hi, h,base_PJ hw hm (out_her M l _ hf hm)]
  unfold ipN; rw [star_sub,mul_sub,trN_sub]

lemma RR0_I (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) :
    RR0 M 1 l f= npt M l (rest f) := by
  rw [RR0_eq _ _ _ _ hf hm isHermitian_one,one_mul,ipnout]
lemma JJ0_I (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) :
    JJ0 M 1 l f= npt M l (vdis f) := by
  rw [JJ0,base_PJ isHermitian_one hm (out_her _ _ _ (sq_test hf) hm),one_mul,
    ipnout,Pj,j_same,one_mul]
  let A := mout M l (bav f)
  have he : trN (A*A) = hsN A := by unfold hsN; rw [show star A=A from out_her _ _ _ hf hm]
  rw [show trN (_* _)=_ from he]
  unfold vdis; rw [n_sub]; unfold A; rw [hsout]; rfl

lemma vpc {T U M D:Mat m} (h:T.IsHermitian) (ha:U.IsHermitian)
    (hm:M.IsHermitian) (hd:D.IsHermitian):
    trN (T*(D*U*M))=trN (T*(M*U*D)) := by
  rw [← trace_star_r]
  simp only [star_mul,show star T=T from h, show star U=U from ha,
    show star M=M from hm,show star D=D from hd]
  rw [trN_cyclic _ T]
  simp only [mul_assoc]

lemma JJ0_eq (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) (hw:W.IsHermitian) :
    let X := mout M l (dis f)
    JJ0 M W l f=
      ipN (W*M) (mout M l (mdis f))-trN (W*(X*star X)) := by
  intro X
  let D := mout M l (bav f)
  let U := uf l f
  let A := mout M l (sqav f)
  have he : X = D-M*U := by
    ext i j
    unfold X D U uf; rw [Matrix.sub_apply,Matrix.mul_diagonal]
    unfold mout dis; simp only [Matrix.of_apply]; ring
  have hh : mout M l (mdis f)=A-(2:ℝ)•(D*U)+M*U*U := by
    ext i j; unfold mdis A D U uf; rw [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
      Matrix.mul_diagonal,Matrix.mul_diagonal,Matrix.mul_diagonal]
    simp [mout]; ring
  have hd : D.IsHermitian := out_her M l _ hf hm
  have hu : U.IsHermitian := uf_sym ..
  have hA : A.IsHermitian := out_her M l _ (sq_test hf) hm
  have hy := vpc hw hu hm hd
  change Pj W M A-Pj W D D = _
  rw [base_PJ hw hm hA,Pj,j_same,he,hh]
  unfold ipN
  simp only [star_add,star_sub,star_smul,star_mul,(show star U=U from hu),
    (show star M=M from hm),(show star D=D from hd),mul_smul_comm,trN_smul,
    sub_mul,mul_sub,mul_add,trN_add,trN_sub,mul_assoc,RCLike.star_def,map_ofNat] -- star reals
  simp only [mul_assoc] at hy; rw [hy]; ring

lemma JJ0_le (f:ℝ→ℝ) (hf:TestF f) (hm:M.IsHermitian) (hw:W.IsHermitian)
    (ht: W ≤ scalar m tmax) :
    ipN (W*M) (mout M l (mdis f)) - JJ0 M W l f ≤
      tmax*npt M l (fun u=> dis f u^2) := by
  let X := mout M l (dis f)
  have h := trN_mul_mono ht (mul_star_self_nonneg X)
  have he : trN ((scalar m tmax)*(X*star X))=tmax*npt M l (fun u=>dis f u^2) := by
    rw [scalar,smul_mul_assoc,one_mul,trN_smul,← hsout]; rfl
  rw [he] at h
  rw [JJ0_eq M W l f hf hm hw]
  simpa [X] using h

lemma BstarP :
    ipN (W*M) (mout M l bstar)=
      ipN (W*M) (mout M l (rest Cp))-ipN (W*M) (mout M l (mdis uc))-
        ipN (W*M) (mout M l (mdis us))-ipN (W*M) (mout M l (mdis qu)) := by
  have h : mout M l bstar=mout M l (rest Cp)-mout M l (mdis uc)-
      mout M l (mdis us)-mout M l (mdis qu) := by
    ext i j; simp only [mout,bstar,rsum,Matrix.sub_apply,Matrix.of_apply]; ring
  unfold ipN; rw [h]; simp_rw [star_sub,mul_sub,trN_sub]

lemma pt26 (hm:M.IsHermitian) (hw:W.IsHermitian)
    (ht: W ≤ scalar m tmax) (h:LayerOK) :
    RR0 M W l Cp-JJ0 M W l uc-JJ0 M W l us-JJ0 M W l qu ≤
      lam*hsN (W*M)+(1/(4*lam))*npt M l (fun u=> bstar u^2)+
        tmax*npt M l dsum := by
  rw [RR0_eq M W l Cp testC hm hw]
  have hi : ipN (W*M) (mout M l bstar) ≤
      lam*hsN (W*M)+(1/(4*lam))*npt M l (fun u=>bstar u^2) := by
    let A := W*M
    let Y := mout M l bstar
    have hj := young_H (-A) Y (show 0<lam by norm_num [lam])
    have hx : ipN (-A) Y= -ipN A Y := by unfold ipN trN; simp [neg_mul]; ring
    have hz : hsN (-A)=hsN A := by unfold hsN; simp
    rw [hx,hz,show hsN Y=_ from hsout M l bstar] at hj
    exact (by unfold lam at *; norm_num at *; unfold A Y at *; linarith)
  rw [BstarP] at hi
  have hh := JJ0_le M W l uc h.c_test hm hw ht
  have he := JJ0_le M W l us h.s_test hm hw ht
  have hu := JJ0_le M W l qu h.q_test hm hw ht
  unfold dsum; rw [n_add,n_add]; unfold tmax at *; linarith
end LPt
end GeneralMahler

end

end OAI

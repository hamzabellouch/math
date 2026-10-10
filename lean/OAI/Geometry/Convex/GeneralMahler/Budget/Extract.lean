import OAI.Geometry.Convex.GeneralMahler.Budget.Blocks

namespace OAI
/-! Frame decomposition of layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ}
lemma bjdiag (b:Fin m→ℝ) (A C:Mat m) :
    trN (A*jprod C (diagonal b)) =
      mats (fun i=>∑ j,A i j*C j i*((b i+b j)/2)) := by
  rw [trace_pair]
  unfold jprod
  congr 1; ext i
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.smul_apply,Matrix.add_apply, Matrix.mul_diagonal,Matrix.diagonal_mul,smul_eq_mul]
  ring
lemma bjdiag' (b:Fin m→ℝ) (A C:Mat m) (ha:A.IsHermitian) (hc:C.IsHermitian) :
    trN (A*jprod C (diagonal b)) =
      mats (fun i=>∑ j,C i j*A j i*((b i+b j)/2)) := by
  rw [bjdiag]; congr 1
  ext i; apply Finset.sum_congr rfl
  intro j _; rw [symm_entry ha,symm_entry hc]; ring
lemma Frm.trNL (u:Frm m) (A:Mat m) : trN (u.loc A)=trN A := by unfold trN; rw [u.loc_trace]
lemma Frm.pjL (u:Frm m) (W A C:Mat m) : Pj (u.loc W) (u.loc A) (u.loc C)=Pj W A C := by
  have he : jprod (u.loc A) (u.loc C)=u.loc (jprod A C) := by
    unfold jprod; rw [u.loc_smul,u.loc_add,u.loc_mul,u.loc_mul]
  unfold Pj; rw [he,← u.loc_mul,u.trNL]
lemma Frm.HL (u:Frm m) {A:Mat m} (h:A.IsHermitian) :
    (u.loc A).IsHermitian := by
  change star (u.loc A)= _
  rw [← u.loc_star,show star A=A from h]

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)
def BL (x:Rn m) (z:ℝ) : block m where
  x := B.ev x
  z := z
  P := (B.Fr x).loc (q.Pmat z x)
  hp := (B.Fr x).loc_psd (q.Pmat_psd ..)
  hi := by
    have h := (B.Fr x).loc_le (q.Pmat_le z x)
    rwa [Frm.loc_one] at h

lemma BLe (x z) : (q.BL B x z).E=(B.Fr x).loc (q.EZ B z x) := by
  unfold BL block.E EZ
  rw [Frm.loc_sub,FieldMat.Θ,B.evfrm]

-- densities of β integrals at a fixed x,z
def linW (f:Plane→ℝ) (u:Plane):=(u.2-u.1)*f u
def bmZ (f:Plane→ℝ) (z:ℝ) (x:Rn m) :=
  Pj 1 (q.EZ B z x) (B.bmat (linW f) z x)
def BB (f:Plane→ℝ) := ∫ x,(∫ z,q.bmZ B f z x) ∂normal m

lemma lin_w {f} (h:Bwt f): Bwt (linW f) :=
  ((Bwt.snd TestF.id).sub (Bwt.fst TestF.id)).mul h
section
variable [NeZero m]

lemma bmMS {f} (h:Bwt f) : mixed (q.bmZ B f)∧StronglyMeasurable (q.bmZ B f).uncurry := by
  have hm := pj_M (1:Mat m) (q.eM B) (B.p_bmat (lin_w h))
  have hh := (pj_cont (1:Mat m)).comp_stronglyMeasurable ((q.eSM B).prodMk
    (B.bsmb (lin_w h)))
  exact ⟨hm,hh⟩
lemma bmh {f} (h:Bwt f) (x) : Integrable (fun z=>q.bmZ B f z x) := by
  have hi := q.bmMS B h
  exact mixed_integrable_left hi.1 x
    ((hi.2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
lemma bmah {f} (h:Bwt f) : Integrable (fun x=>∫ z,q.bmZ B f z x) (normal m) := by
  have hi := q.bmMS B h
  exact (mixed_integrable (μ:=volume) (ν:=normal m) hi.1 hi.2.aestronglyMeasurable).integral_prod_right

end

lemma bm_trace (x z f) :
    let b := q.BL B x z
    q.bmZ B f z x=mats (fun i=> b.S i i*f (z,b.x i)) := by
  intro b
  let u := B.Fr x
  rw [bmZ, ← u.pjL]
  rw [u.loc_one,← q.BLe,B.bmat_loc,Pj,one_mul,trN_j,traceDiag]
  congr 1; ext i
  change b.E i i *linW f (z,b.x i)=_
  unfold linW
  rw [b.Sdiag,b.az]
  rw [show b.z=z from rfl]; ring

lemma LL_Bw (x z) {f:Plane→ℝ} (hf:Bwt f) :
    q.lk B 1 f z x=q.bmZ B (bAv f) z x := by
  unfold lk bmZ
  congr 2
  funext u
  exact hf.bar_eq u
section
variable [NeZero m]

lemma bm_pos (x z) (f:Plane→ℝ) (h:∀ w,0≤f w) :
    0 ≤ q.bmZ B f z x := by
  rw [q.bm_trace]
  unfold mats
  apply div_nonneg _ m_pos.le
  apply Finset.sum_nonneg
  intro i _; apply mul_nonneg
  · exact (q.BL B x z).Spar.posSemidef.diag_nonneg
  apply h

end

lemma pairing_layer (x z) {f:Plane→ℝ} (hf:Bwt f) (ht:T.IsHermitian) :
    let b:=q.BL B x z
    let u:=B.Fr x
    let t:=u.loc T
    q.lk B T f z x =
      trN (b.S*jprod t (diagonal (fun i=> bAv f (z,b.x i)))) +
        mats (fun i=>∑ j,b.E i j*t j i*kz f (b.x i) (b.x j) z) := by
  intro b u t
  rw [bjdiag,lk,← u.pjL,← q.BLe,B.bmat_loc,Pj,bjdiag']
  · rw [← mats_add]
    congr 1; ext i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    change b.E i j*t j i*((bInt f (z,b.x i)+bInt f (z,b.x j))/2)=_
    unfold kz
    have he : b.S i j=rcoef (b.x i) (b.x j) z*b.E i j := rfl
    rw [he,hf.bar_eq,hf.bar_eq]
    dsimp only []; ring
  · exact u.HL ht
  exact b.Her
lemma bm_add (x z) (f g:Plane→ℝ) :
    q.bmZ B (fun w=>f w+g w) z x=q.bmZ B f z x+q.bmZ B g z x := by
  simp_rw [bm_trace]; rw [← mats_add]
  congr 1; ext; ring
lemma bm_scale (x z) (f:Plane→ℝ) (a:ℝ) :
    q.bmZ B (fun w=>a*f w) z x=a*q.bmZ B f z x := by
  simp_rw [bm_trace]; rw [← mats_s]; congr 1; ext; ring
end ProjField
end GeneralMahler

end

end OAI

import OAI.Geometry.Convex.GeneralMahler.GradientLayer

namespace OAI
/-! Eq13 coefficient-pair (weighted K multiplier via coefficients). -/
noncomputable section
open Set Filter Metric MeasureTheory MeasureTheory.Measure Matrix Real
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

def Pj (B A C:Mat m) := trN (B*jprod A C)
def Pt (B:Mat m) (A C:Rn m→Mat m) := ∫ x,Pj B (A x) (C x) ∂normal m

def PJ (B:Mat m) : Mat m→L[ℝ]Mat m→L[ℝ]ℝ :=
  let u := (1/2:ℝ) • ((ContinuousLinearMap.mul ℝ (Mat m))+
    (ContinuousLinearMap.mul ℝ (Mat m)).flip)
  (ContinuousLinearMap.compL ℝ _ _ _ (etL B)).comp u
omit [NeZero m] in
lemma pJ_eq (B A C:Mat m) : PJ B A C=Pj B A C := by simp [PJ,Pj,jprod,mul_add, trN_add,trN_smul,etL_apply]

def CpPair (B:Mat m) (A C:Rn m→Mat m) (a:MI m) := Pj B (cof A a) (cof C a)
def kMode (a:MI m) : ℝ := (1+(deg a:ℝ))⁻¹
def KP (B:Mat m) (A C:Rn m→Mat m) := ∑' a,CpPair B A C a*kMode a

lemma pt_sum {B:Mat m} {A C:Rn m→Mat m} (ha:regular A) (hc:regular C) :
    HasSum (CpPair B A C) (Pt B A C) := by
  have hi := cof_bil ha hc (PJ B)
  simp_rw [pJ_eq] at hi; exact hi

omit [NeZero m] in
lemma summable_k {f:MI m→ℝ} (hf:Summable f) :
    Summable (fun a=> f a*kMode a) := by
  apply Summable.of_norm_bounded hf.norm
  intro a
  have he : 0 ≤ (deg a:ℝ) := by exact_mod_cast Nat.zero_le _
  have hc : 0 < 1+(deg a:ℝ) := by linarith
  unfold kMode
  rw [norm_mul,Real.norm_of_nonneg (inv_pos.mpr hc).le]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [← one_div,div_le_iff₀ hc]; linarith

lemma K_sum {B:Mat m} {A C:Rn m→Mat m} (ha:regular A) (hc:regular C) :
    Summable (fun a=> CpPair B A C a*kMode a) := summable_k (pt_sum ha hc).summable

namespace ProjField
variable (q:ProjField m)
lemma regH {f:ℝ→ℝ} (hf:TestF f) : regular (q.Hmat f) :=
  ⟨q.H_poly hf.der.poly,q.H_SM.aestronglyMeasurable⟩
lemma cfH_sym {f} (hf:TestF f) (a:MI m) :
    (cof (q.Hmat f) a).IsHermitian :=
  hermitian_integral (i_cof (q.H_poly hf.der.poly) q.H_SM.aestronglyMeasurable a)
    (ae_of_all _ fun x=> (q.H_hermitian hf.der.poly _).smul (by simp [IsSelfAdjoint]))
lemma pj_sum {A C:Mat m} (hA:A.IsHermitian) (hC:C.IsHermitian) :
    (∑ i,⟪q.act i A,q.act i C⟫)=(m:ℝ)*Pj q.covMat A C := by
  let s := q.S
  have he (A C:Mat m) (ha:A.IsHermitian) :
      trace (q.covMat*(A*C))=∑ i,⟪q.act i A,q.act i C⟫ := by
    rw [q.trace_SPS]
    apply Finset.sum_congr rfl; intro i _
    rw [_root_.map_mul]
    change ⟪op s (e i),op A (op C (op s (e i)))⟫ = _
    rw [← op_iff_hermitian.mp ha]; rfl
  unfold Pj jprod trN
  rw [mul_smul_comm,mul_add,trace_smul,trace_add,he _ _ hA, he _ _ hC]
  have hp : (∑ i,⟪q.act i C,q.act i A⟫)=(∑ i,⟪q.act i A,q.act i C⟫) :=
    Finset.sum_congr rfl fun i _=> real_inner_comm ..
  rw [hp,smul_eq_mul]
  have h:= m_pos (m:=m)
  field_simp; ring

lemma pt_k_cov {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    (∫ x,⟪q.WH f x,q.WH g x⟫ ∂normal m)/(m:ℝ) =
      KP q.covMat (q.Hmat f) (q.Hmat g) := by
  let S : MI m→ℝ := fun a=> ⟪cof (q.WH f) a,cof (q.WH g) a⟫
  let A := q.Hmat f
  let B := q.Hmat g
  let aR := fun i a=> q.act i (cof A a)
  let bR := fun i a=> q.act i (cof B a)
  let I := fun (i:Fin m) (a:MI m)=> ⟪aR i a,bR i a⟫*kMode a
  have hu (a:MI m) (i:Fin m) :
      S (inc a i)*((a i+1:ℕ):ℝ)/(1+deg a)=I i a := by
    have hf' : aR i a= _ := q.WH_rec hf i a
    have hg' : bR i a= _ := q.WH_rec hg i a
    unfold I; rw [hf',hg',real_inner_smul_left,real_inner_smul_right,← mul_assoc,← pow_two,snsq]
    unfold S kMode; ring
  have hp : HasSum S (∫ x,⟪q.WH f x,q.WH g x⟫ ∂normal m) :=
    cof_vec _ _ (q.WH_reg hf) (q.WH_reg hg)
  have hZ : S 0=0 := by
    unfold S cof
    simp [MM,H,q.WH_mean hf]
  have h := sum_spectral S hZ hp.summable
  simp_rw [hu] at h
  have hi (i:Fin m) : Summable (I i) := by
    have ha := q.regH hf
    have hb := q.regH hg
    have hh := (cof_vec (fun x=>q.act i (A x)) (fun x=>q.act i (B x)) (ha.lin _) (hb.lin _)).summable
    apply summable_k
    unfold aR bR A B
    simp_rw [cof_clm ha,cof_clm hb]
    exact hh
  have heq (a) : ∑ i,I i a=(m:ℝ)*(CpPair q.covMat A B a*kMode a) := by
    unfold I aR bR CpPair
    rw [← Finset.sum_mul,q.pj_sum (q.cfH_sym hf _) (q.cfH_sym hg _),mul_assoc]
  rw [← Summable.tsum_finsetSum fun i _=>hi i] at h
  simp_rw [heq] at h; rw [tsum_mul_left] at h
  rw [← hp.tsum_eq,h]
  change _/(m:ℝ)=∑' a,CpPair q.covMat A B a*kMode a
  have hx:=m_pos (m:=m); field_simp

end ProjField
end GeneralMahler

end

end OAI

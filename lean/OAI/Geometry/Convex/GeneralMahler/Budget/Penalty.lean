import OAI.Geometry.Convex.GeneralMahler.Budget.Tbound

namespace OAI
/-! Constant-layer penalty and commutator remainder accounting. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)
def NK (T:Mat m) := q.Nt T (fun x=>x) (fun x=>x)
lemma nn_eq : q.NK 1=eNt q.edge := by
  rw [eNt, integral_integral_swap q.edge.n0_int]
  unfold NK Nt nTK Edge.nt0; simp
lemma NKpos : 0≤q.NK 1 := by
  rw [q.nn_eq]; unfold eNt
  apply integral_nonneg; intro u
  exact integral_nonneg (fun x=>q.edge.nt_pos ..)

lemma lm_pos : 0 < lm := by norm_num [lm,bb,eta,kar,tmin]
lemma karp : 0 < kar := by norm_num [kar]
omit [NeZero m] in
lemma LL1 (W:Mat m) :
    q.LLw B W (fun _=>1)=q.be B W (fun x=>x) (fun x=>x) := by
  have h := q.Le_id B W TestF.id TestF.id; simpa using h
lemma NZ_A (W:Mat m) :
    q.NK W=2*q.LLw q.FA W (fun _=>1) := by
  rw [q.LL1]
  have hh : q.MB q.FA (fun x=>x)=fun _ =>0 := by
    funext x
    rw [MB,id_ga]
    have he : q.FA.eval (fun x=>x) x=q.Amat x :=
      cfc_id' ℝ _ (ha:= show IsSelfAdjoint (q.FA.A x) from q.FA.sym _)
    rw [he]
    change q.Amat _-_+scalar _ _=_
    simp [scalar]
  have ht := q.eq15 q.FA W TestF.id
  rw [hh] at ht
  have hi : Pt W (fun _=>0) (fun _=>0)=0 := by simp [Pt,Pj,jprod,trN]
  rw [hi] at ht
  unfold NK; linarith
lemma NZ_L (W:Mat m) :
    Pt W q.RR q.RR+q.NK W=2*q.LLw q.FL W (fun _=>1) := by
  rw [q.LL1]
  have h := q.eq15 q.FL W TestF.id
  rw [q.MB_id] at h
  unfold NK; linarith

lemma const_limit (ht:T∈specBox m tmin tmax) :
    -kar*q.NK T≤ -kar*tmin*q.NK 1+lm*q.NK 1+e₀*Hcomm q.Amat T := by
  let f := fun _:Plane=> (1:ℝ)
  have he (z:ℝ) (l:Fin m→ℝ) (t:Mat m) (he:t∈specBox m tmin tmax) :
      Matrix.diagonal (fun i:Fin m=>2*tmin)≤
        (2:ℝ) • jprod t (Matrix.diagonal (fun i=> bAv f (z,l i))) := by
    unfold f; simp_rw [bar_const]
    rw [show (Matrix.diagonal (fun _:Fin m=> (1:ℝ)))=1 from rfl]
    have hi : jprod t 1=t := by unfold jprod; simp only [one_mul,mul_one]; module
    rw [hi]
    apply le_trans _ (smul_le_smul_of_nonneg_left he.2.1 (show (0:ℝ)≤2 by norm_num))
    apply le_of_eq
    unfold scalar; ext i j
    by_cases h:i=j
    · subst j; simp
    simp [h]
  have hl : 0 < 2*lm/kar := by have h := karp; have he := lm_pos; positivity
  have hf : Bwt f := Bwt.const _
  have h := q.Klimit q.FA T ht hf hf (Bwt.const (2*tmin)) (fun _=>zero_le_one)
    2 (by norm_num) he Ux (2*Real.log 2-1/3) Ux_area (fun _ _ _ _ _=> ux_nn)
    (fun x y z hx hy=> by
      have H := (pairEst f hf hx hy).2
      unfold Om at H; simp_rw [bar_const] at H; exact H) hl
  have hh : q.BB q.FA (fun _=>2*tmin)=2*tmin*q.BB q.FA f :=
    by simpa only [f,mul_one] using q.BB_scale q.FA f (2*tmin)
  rw [hh] at h
  have h₁:= q.NZ_A T
  have h₂ := q.NZ_A (1:Mat m)
  rw [q.BB1] at h₂
  have hi := mul_le_mul_of_nonneg_left h karp.le
  have hv : kar*((2 * Real.log 2-1/3)/(4*(2*lm/kar))) ≤ e₀ := by
    unfold kar lm e₀ bb eta tmin kar
    have hj:= Real.log_two_lt_d9; norm_num at *; linarith
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤ Hcomm q.Amat T from
    integral_nonneg fun _=> hsN_pos _)
  unfold f at *
  change -kar*q.NK T≤ -kar*tmin*q.NK 1+lm*q.NK 1+e₀*Hcomm q.FA.A T
  change kar* _ * Hcomm q.FA.A T≤ e₀*Hcomm q.FA.A T at hp
  unfold lm kar bb eta tmin e₀ at *; norm_num at *; linarith

omit [NeZero m] in
lemma cmCL (T:Mat m) : ∃ l: Mat m→L[ℝ]Mat m,(l:Mat m→Mat m)=fun x=>cmu x T := by
  let l := ContinuousLinearMap.mul ℝ (Mat m)
  exact ⟨l.flip T-l T,rfl⟩
lemma C_Hcomm (hT:T.IsHermitian) {A:Rn m→Mat m} (ha:regular A) (h:∀ x,(A x).IsHermitian) :
    HasSum (fun a=> (- CpPair 1 (fun x=> cmu (A x) T) (fun x=>cmu (A x) T) a)) (Hcomm A T) := by
  obtain ⟨l,hl⟩ := cmCL T
  have hc : regular (fun x=>cmu (A x) T) := by simp_rw [← congrFun hl]; exact ha.lin l
  have hi := (pt_sum (B:=(1:Mat m)) hc hc).neg
  have he (x) : hsN (cmu (A x) T) = -Pj 1 (cmu (A x) T) (cmu (A x) T) := by
    rw [hsN,Pj,one_mul,j_same]
    have hh : star (cmu (A x) T)= -cmu (A x) T := by
      unfold cmu; rw [star_sub,star_mul,star_mul, (show star (A x)=_ from h x), (show star T=T from hT),neg_sub]
    rw [hh,mul_neg]
    unfold trN; rw [trace_neg]; ring
  unfold Hcomm; simp_rw [he,integral_neg]
  exact hi

lemma comm_split (hT:T.IsHermitian) (h:q.avgA=0) :
    Hcomm q.Amat T= Hcomm q.Lmat T+Hcomm q.RR T := by
  obtain ⟨l,hl⟩ := cmCL T
  have hi := C_Hcomm T hT q.a_reg fun x=> q.H_hermitian poly_id_der _
  have h₁ := C_Hcomm T hT q.l_reg q.L_sym
  have h₂ := C_Hcomm T hT q.R_reg q.r_sym
  apply HasSum.unique hi
  apply (h₁.add h₂).congr_fun
  intro a
  have he {A:Rn m→Mat m} (ha:regular A) :
      CpPair 1 (fun x=>cmu (A x) T) (fun x=>cmu (A x) T) a=
        Pj 1 (l (cof A a)) (l (cof A a)) := by
    unfold CpPair
    simp_rw [cof_clm ha,congrFun hl]
  rw [he q.a_reg,he q.l_reg,he q.R_reg]
  have hh : cof q.Amat a = cof q.Lmat a + cof q.RR a := by
    unfold RR; rw [cof_subm q.a_reg q.l_reg]; abel
  by_cases ha:deg a=1
  · rw [hh,q.bal_cf h a (by omega)]; simp [Pj,jprod,trN]
  rw [hh,q.coL_o ha]; simp [Pj,jprod,trN]

omit [NeZero m] in
lemma comm_est (ht:T∈specBox m tmin tmax) {A:Mat m} (ha:A.IsHermitian) :
    hsN (cmu A T) ≤ (2*tr)^2*Pj 1 A A := by
  let t := T
  let u := Frm.eu ht.1
  have he := u.loc_s
  let f := u.eig T
  have hi (i:Fin m) : tmin≤f i ∧ f i≤tmax := by
    have h := spectrum_order T ht.1 (l:=tmin) (r:=tmax)
    have hi : f i∈ spectrum ℝ T := by
      unfold f u
      rw [ht.1.spectrum_real_eq_range_eigenvalues,Frm.eu_eig]; exact ⟨i,rfl⟩
    exact ⟨h.1.mp ht.2.1 _ hi,h.2.mp ht.2.2 _ hi⟩
  have hh : hsN (cmu A T)=hsN (cmu T A) := by
    rw [show cmu A T = -cmu T A from by unfold cmu; rw [neg_sub] ]
    simp [hsN]
  have hb : Pj 1 A A=hsN A := by rw [Pj, j_same,one_mul,hsN,show star A=A from ha]
  rw [hh,hb,cmu_eig T A u (Frm.eu_d _), ← hsN_loc A u,hsN_eq, mats_s2]
  apply mats_le
  intro i
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h₁:=hi i; have h₂:=hi j
  change (f i-f j)^2≤ _
  unfold tmin tmax Profile.tr at *
  nlinarith
lemma comm_bound (ht:T∈specBox m tmin tmax) :
    Hcomm q.RR T≤ (2*tr)^2*Pt 1 q.RR q.RR := by
  unfold Hcomm Pt; rw [← integral_const_mul]
  exact integral_mono (ck_i q.R_reg T) ((pj_poly_part q.R_reg _).const_mul _)
    fun x=> comm_est T ht (q.r_sym x)
end ProjField
end GeneralMahler

end

end OAI

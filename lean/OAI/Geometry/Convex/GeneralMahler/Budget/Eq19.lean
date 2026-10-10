import OAI.Geometry.Convex.GeneralMahler.Budget.Degree

namespace OAI
/-! Budgets on remainder by Hermite degree. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Layers HMode Profile
variable {m:ℕ} [NeZero m]

lemma sigEQ {q:ProjField m} (h:LayerOK) (a:MI m) :
    2*q.sigterm FF a =
      4*cc*kMode a*Pj q.covMat (cof q.RR a) (cof q.RR a)+
      4*kk*Pj q.covMat (cof q.RR a) (q.DD qu a) := by
  rw [ProjField.sigterm,q.D_F h,p_ladd,pJ_smul_right,pJ_smul_right]
  ring

omit [NeZero m] in
lemma odd_budget (W X Y:Mat m) (hw:0≤W) (hx:X.IsHermitian) (hy:Y.IsHermitian)
    (k:ℝ) (hk:0<k) (hr:k≤1/4) :
    4*cc*k*Pj W X X+4*kk*Pj W X Y-k⁻¹*Pj W Y Y ≤ bb*Pj W X X := by
  have he := pj_positive hw (hy.sub (hx.smul (show IsSelfAdjoint (2*kk*k) from rfl)))
  rw [p_square_diff,pj_sym W Y X] at he
  calc
    _ ≤ (4*cc*k+4*kk^2*k)*Pj W X X := by
      field_simp; nlinarith
    _ = 4*bb*k*Pj W X X := by rw [k_sq]; ring
    _ ≤ _ := by
      have hh := pj_positive hw hx
      have h₁ : 4*bb*k ≤ bb := by unfold bb; linarith
      exact mul_le_mul_of_nonneg_right h₁ hh

def bmp : ℝ := bm/(1+tmax)
lemma bmp_pos : 0<bmp := by unfold bmp bm bb cc eta tmax; norm_num
lemma bm_pos : 0<bm := by unfold bm bb cc eta tmax; norm_num

omit [NeZero m] in
lemma even_budget (W X Y:Mat m) (hw:0≤W) (hx:X.IsHermitian) (hy:Y.IsHermitian)
    (k:ℝ) (hk:0<k) (hr:k≤1/3) :
    4*cc*k*Pj W X X+4*kk*k*Pj W X Y-k*Pj W Y Y ≤ (bb+eta)*Pj W X X+bmp*Pj W Y Y := by
  let a := bb+eta-4*cc*k
  have ha : 0<a := by unfold a bb eta cc; linarith
  let m := 2*kk*k
  have he := pj_positive hw (hx.sub (hy.smul (show IsSelfAdjoint (m/a) from rfl)))
  rw [p_square_diff] at he
  have H : m^2≤a*(bmp+k) := by
    have h₁ : a*(bmp+k)-m^2=(1-3*k)*((bb+eta)*bmp+4*bb/3*k) := by
      unfold a m
      rw [mul_pow,mul_pow,k_sq]
      unfold bmp bm bb cc eta tmax
      ring
    rw [← sub_nonneg,h₁]
    have h := bmp_pos
    have hv : 0≤1-3*k:=by linarith
    exact mul_nonneg hv (by unfold bb eta; positivity)
  have hh : 2*m*Pj W X Y≤ a*Pj W X X + m^2/a*Pj W Y Y := by
    field_simp at he ⊢
    nlinarith
  have ht := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mpr (H.trans_eq (mul_comm ..)))
    (pj_positive hw hy)
  unfold a m at *
  linarith

namespace ProjField
variable (q:ProjField m)
omit [NeZero m] in
lemma cov_bound {T:Mat m} (ht:T ∈ specBox m tmin tmax) (he:1+T=q.covMat) :
    q.covMat ≤ scalar m (1+tmax) := by
  rw [← he,scalar, add_smul,one_smul]
  exact add_le_add le_rfl ht.2.2
lemma sig_one_degree (hs:LayerOK) (hh:q.avgA=0)
    {T:Mat m} (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) (a:MI m) :
    let W := q.covMat
    2*q.sigterm FF a - q.Dterm qu a ≤
      (bb+eta)*CpPair W q.RR q.RR a-eta*CpPair W q.Ro q.Ro a+
      bm*CpPair 1 (q.MB q.FL (fl qu)) (q.MB q.FL (fl qu)) a := by
  intro W
  let X := cof q.RR a
  let Y := q.DD qu a
  let Q := cof (q.MB q.FL (fl qu)) a
  set k := kMode a
  have hk := rho_pos a
  have hw : 0≤W := pos_cov
  have hf := fl_test hs.q_test
  have hx : X.IsHermitian := Cf_sym q.R_reg q.r_sym a
  have hy : Y.IsHermitian := q.DD_sym hs.q_test a
  have hQ : Q.IsHermitian := Cf_sym (q.mb_reg q.FL hf) (fun x=> q.P_mb_sym hf x) a
  rw [sigEQ hs]
  unfold CpPair Dterm
  rw [← rho_inv]
  have hz := pj_positive (show 0 ≤ (1:Mat m) from (Matrix.PosSemidef.one).nonneg) hQ
  change 4*cc*k*Pj W X X+4*kk*Pj W X Y-k⁻¹*Pj W Y Y ≤
    (bb+eta)*Pj W X X-eta*Pj W (cof q.Ro a) (cof q.Ro a)+bm*Pj 1 Q Q
  rw [q.coRo]
  by_cases h:deg a<2
  · have he : X=0 := q.bal_cf hh a h
    have hu : cof q.RR a=0 := he
    rw [he,hu]
    have h₀ (B:Mat m) : Pj W 0 B=0 := by simp [Pj,jprod,trN]
    simp_rw [ite_self,h₀,mul_zero,add_zero]
    have hy' := pj_positive hw hy
    have hb := bm_pos; have hi : 0 ≤ k⁻¹ := by exact (inv_pos.mpr hk).le
    nlinarith
  have hh : k≤1/3 := by
    unfold k kMode
    rw [← one_div, div_le_iff₀ (by positivity)]
    have hi : 2 ≤ deg a := by omega
    have h₂ : (2:ℝ) ≤ deg a := by exact_mod_cast hi
    linarith
  split_ifs with ha
  · have hu : Y=k• Q := q.D_e hs a ha
    rw [hu,pJ_smul_right,pJ_smul_right,pJ_smul_left,show Pj W 0 0=0 from by simp [Pj,jprod,trN] ]
    have hb := even_budget W X Q hw hx hQ k hk hh
    have hl := p_le_p (q.cov_bound ht he) hQ
    have hl' : Pj (scalar m (1+tmax)) Q Q = (1+tmax)*Pj 1 Q Q := by
      simp only [scalar,Pj,smul_mul_assoc,trN_smul]
    rw [hl'] at hl
    have heq : bmp*(1+tmax)=bm := by unfold bmp tmax; field_simp
    have hi := mul_le_mul_of_nonneg_left hl bmp_pos.le
    have hu : k⁻¹*(k*(k*Pj W Q Q))=k*Pj W Q Q := by field_simp
    rw [hu]
    rw [← mul_assoc,heq] at hi
    linarith
  change _≤ (bb+eta)*Pj W X X-eta*Pj W X X+ _
  have h' : 3≤deg a := by
    obtain ⟨n,hn⟩ := Nat.not_even_iff_odd.mp ha
    omega
  have hx' : k ≤ 1/4 := by
    unfold k kMode
    rw [← one_div, div_le_iff₀ (by positivity)]
    have h : (3:ℝ)≤deg a := by exact_mod_cast h'
    linarith
  have h := odd_budget W X Y hw hx hy k hk hx'
  linarith [mul_nonneg bm_pos.le hz]

lemma degree19 (hs:LayerOK) (hh:q.avgA=0)
    {T:Mat m} (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) :
    q.sigma FF-q.DVec ≤
      (bb+eta)*Pt q.covMat q.RR q.RR-eta*Pt q.covMat q.Ro q.Ro +
      bm*Pt 1 (q.MB q.FL (fl qu)) (q.MB q.FL (fl qu)) := by
  let W := q.covMat
  have hu := (pt_sum (B:=W) q.R_reg q.R_reg).mul_left (bb+eta)
  have hv := (pt_sum (B:=W) q.Ro_reg q.Ro_reg).mul_left eta
  have hp := q.mb_reg q.FL (fl_test hs.q_test)
  have hx := ((hu.sub hv).add ((pt_sum (B:=1) hp hp).mul_left bm))
  have h := ((q.sig_split hs.f_test).mul_left 2).sub (q.H_K_split hs.q_test)
  have hb := hasSum_le (fun a=> q.sig_one_degree hs hh ht he a) h hx
  have hi := (q.sig_split hs.f_test).tsum_eq
  have hj := (q.H_K_split hs.q_test).tsum_eq
  unfold sigma DVec Dnorm
  rw [hi,hj]
  have hc := q.D_pos hs.c_test; have hd := q.D_pos hs.s_test
  unfold Dnorm at hc hd
  linarith

lemma NTpos19 (hs:LayerOK) :
    Pt 1 (q.MB q.FL (fl qu)) (q.MB q.FL (fl qu)) ≤
      2*q.LLw q.FL 1 (fun u=>N2 qu u.1*N2 qu u.2) := by
  have h := hs.q_test; have hp := fl_test h; let f := fl qu
  have ht : 0≤q.Nt 1 f f := by
    apply integral_nonneg; intro x; apply integral_nonneg; intro u
    dsimp only [nTK,f,Pi.zero_apply]; rw [fl_d h,one_mul]
    exact mul_nonneg (mul_nonneg (hs.sq_p _).le (hs.sq_p _).le) (q.edge.nt_pos ..)
  rw [q.eq15 _ _ hp,← q.Le_id q.FL 1 hp hp,fl_d h]
  linarith
end ProjField
end GeneralMahler

end

end OAI

import OAI.Geometry.Convex.GeneralMahler.Budget.Parity

namespace OAI
/-! Per Gaussian degree proof of the form estimate Eq19. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile HMode Layers
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma j_same (A:Mat m) : jprod A A=A*A := by unfold jprod; module
omit [NeZero m] in
lemma pj_positive {W A:Mat m} (h:0≤W) (hh:A.IsHermitian) : 0≤ Pj W A A := by
  rw [Pj,j_same]
  exact trN_mul_nonneg h (sqPSD hh)
omit [NeZero m] in
lemma p_le_p {W T A:Mat m} (h:W≤T) (hh:A.IsHermitian) :
    Pj W A A≤ Pj T A A := by simp only [Pj,j_same]; apply trN_mul_mono h (sqPSD hh)
omit [NeZero m] in
lemma p_ladd (W A B C:Mat m) : Pj W A (B+C)= Pj W A B+Pj W A C := by
  simp_rw [← pJ_eq]; rw [_root_.map_add]
omit [NeZero m] in
lemma p_square_diff (W A B:Mat m) (c:ℝ) :
    Pj W (A-c•B) (A-c•B)=Pj W A A-2*c*Pj W A B+c^2*Pj W B B := by
  simp_rw [pj_ss,pJ_smul_left,pJ_smul_right]; rw [pj_sym W B A]; ring

omit [NeZero m] in
lemma pos_cov {q:ProjField m} : 0≤q.covMat := sqPSD q.pos.isHermitian
omit [NeZero m] in
lemma Cf_sym {A:Rn m→Mat m} (ha:regular A) (hh:∀ x,(A x).IsHermitian) (a:MI m) :
    (cof A a).IsHermitian := hermitian_integral (i_cof ha.p ha.meas a)
      (ae_of_all _ fun x=> (hh x).smul (show IsSelfAdjoint (_:ℝ) from rfl))

omit [NeZero m] in
lemma rho_pos (a:MI m) : 0<kMode a := by unfold kMode; positivity
omit [NeZero m] in
lemma rho_inv (a:MI m) : (kMode a)⁻¹=1+(deg a:ℝ) := by unfold kMode; rw [inv_inv]
namespace ProjField
variable (q:ProjField m)
lemma DD_sym {l:ℝ→ℝ} (hl:TestF l) (a:MI m) :
    (q.DD l a).IsHermitian := by
  unfold DD
  refine ((q.cfH_sym (fl_test hl) _).smul (by simp [IsSelfAdjoint])).sub
    (Cf_sym (q.FL.eval_reg (pl_test hl)) (fun _=> cfc_herm ..) _)
lemma r_sym (x) : (q.RR x).IsHermitian :=
  (q.H_hermitian poly_id_der x).sub (q.L_sym x)

lemma P_mb_sym {l} (hl:TestF l) (x) : (q.MB q.FL l x).IsHermitian :=
  ((q.H_hermitian hl.der.poly x).sub (cfc_herm ..)).add (scalar_sym ..)
lemma D_pos {l} (hl:TestF l) : 0 ≤ q.Dnorm l :=
  tsum_nonneg (fun a=> mul_nonneg (by positivity) (pj_positive pos_cov (q.DD_sym hl _)))

-- linearity of D in test l
lemma pl_scale {l} (_hl:TestF l) (a:ℝ) :
    pl (fun t=>a*l t)=fun t=>a*pl l t := by
  have h : prim (fun t=>a*l t)=fun t=>a*prim l t := by
    funext x; unfold prim; rw [intervalIntegral.integral_const_mul]
  unfold pl; rw [h,ga_mul]; ext; ring
lemma d_cmul (l:ℝ→ℝ) (hl:TestF l) (a:ℝ) :
    deriv (fun t=>a*l t) =fun t=>a*deriv l t :=
  funext fun x=> ((hl.diff x).hasDerivAt.const_mul a).deriv
lemma fl_s {l} (hl:TestF l) (a:ℝ) :
    fl (fun t=>a*l t)=fun t=>a*fl l t := by
  unfold fl; rw [pl_scale hl]; unfold Nr N
  rw [d_cmul _ (pl_test hl),d_cmul _ (pl_test hl).der]
  ext; ring
lemma D_s (l:ℝ→ℝ) (hl:TestF l) (a:ℝ) (x:MI m) :
    q.DD (fun t=>a*l t) x=a•q.DD l x := by
  unfold DD; rw [fl_s hl,pl_scale hl,show q.FL.eval (fun t=>a*pl l t) =_ from funext
    (fun x=>q.FL.eval_scale (pl_test hl) a x)]
  have he : q.Hmat (fun t=>a*fl l t)=fun t=>a•q.Hmat (fl l) t := by
    funext t; unfold Hmat kerH; rw [d_cmul _ (fl_test hl)]
    simp_rw [mul_smul,integral_smul]
  rw [he,cf_s,cf_s]; module
lemma Hd_sub (l j:ℝ→ℝ) (hl:TestF l) (hj:TestF j) :
    q.Hmat (fun x=>l x-j x)=fun x=> q.Hmat l x-q.Hmat j x := by
  funext x
  have he (z) : q.kerH (fun x=>l x-j x) z x=q.kerH l z x-q.kerH j z x := by
    unfold kerH; rw [drv_sub hl hj,sub_smul]
  unfold Hmat; simp_rw [he]; rw [integral_sub (q.H_left_int hl.der.poly x) (q.H_left_int hj.der.poly x)]
lemma D_sub {l j} (hl:TestF l) (hj:TestF j) (a:MI m) :
    q.DD (fun x=>l x-j x) a=q.DD l a-q.DD j a := by
  unfold DD
  have he : fl (fun x=>l x-j x) = fun x=>fl l x-fl j x := by
    unfold fl; rw [pl_sub hl hj]; unfold Nr; rw [N_sub (pl_test hl) (pl_test hj)]
    funext x; ring
  rw [he,pl_sub hl hj,q.Hd_sub _ _ (fl_test hl) (fl_test hj),cof_subm (q.regH
    (fl_test hl)) (q.regH (fl_test hj))]
  simp_rw [show q.FL.eval (fun x=>_ - _) = _ from (funext fun x=> q.FL.eval_sub (pl_test hl) (pl_test hj) x)]
  rw [cof_subm (q.FL.eval_reg (pl_test hl)) (q.FL.eval_reg (pl_test hj))]; module

lemma D_c1 (a:MI m) :
    q.DD (fun _=>1) a=(2*kMode a) • cof q.RR a := by
  let k := fun _:ℝ=> (1:ℝ)
  let i := fun x:ℝ=>x
  have he : prim k=i := by funext x; unfold prim k i; simp
  have hh : pl k=i := by unfold pl; rw [he,id_ga]; funext x; ring
  have hh' : fl k=fun x=>2*x := by unfold fl; rw [hh]; funext x; unfold i Nr N; simp; ring
  have hp : q.Hmat (fl k)=fun x=> (2:ℝ)•q.Amat x := by
    funext t
    unfold Amat Hmat kerH; rw [hh']
    have he : deriv (fun x:ℝ=>2*x) =fun x=>2 := by ext; simp
    simp_rw [he,deriv_id, one_smul, integral_smul]
  change q.DD k a=_
  unfold DD
  rw [hh,show q.FL.eval i=q.Lmat from funext q.evId,hp,cf_s]
  unfold RR; rw [cof_subm q.a_reg q.l_reg]
  by_cases h:deg a=1
  · rw [kMode,h]; push_cast; module
  rw [q.coL_o h]; module

lemma D_F (h:LayerOK) (a:MI m) :
    q.DD FF a=(2*cc*kMode a) • cof q.RR a+(2*kk)• q.DD qu a := by
  let f := fun _:ℝ=>(1:ℝ)
  have hh : FF=fun x=> cc*f x - (-2*kk)*qu x := by funext x; unfold FF f; ring
  rw [hh,q.D_sub ((TestF.const _).mul (TestF.const _)) ((TestF.const _).mul h.q_test),
    q.D_s f (TestF.const _),q.D_s qu h.q_test,q.D_c1]; module
lemma D_e (h:LayerOK) (a:MI m) (he:Even (deg a)) :
    q.DD qu a=kMode a • cof (q.MB q.FL (fl qu)) a := by
  have hh := h.q_test
  have he' : q.MB q.FL (fl qu)=fun x=> q.Hmat (fl qu) x-q.FL.eval (fl qu) x := by
    funext x; rw [MB,fl_ga hh]; simp [scalar]
  unfold DD
  rw [he',cof_subm (q.regH (fl_test hh)) (q.FL.eval_reg (fl_test hh))]
  have hf := cof_odd_zero _ a he (q.BoEval (fl_odd _ hh h.q_even))
  have hg := cof_odd_zero _ a he (q.BoEval (pl_odd _ hh h.q_even))
  rw [hf,hg]; module
end ProjField
end GeneralMahler

end

end OAI

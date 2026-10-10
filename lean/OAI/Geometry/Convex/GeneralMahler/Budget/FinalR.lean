import OAI.Geometry.Convex.GeneralMahler.Budget.Penalty

namespace OAI
/-! Interaction with R and cost of Sigma. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile HMode
variable {m:ℕ}
lemma Veven : Function.Even Profile.v := by
  intro x; rw [v_log,v_log,neg_neg]; ring
lemma trace_star_r (A:Mat m) : trN (star A)=trN A := by unfold trN; rw [show star A=Aᴴ from rfl,trace_conjTranspose]; rfl
lemma pj_cyc3 {X T A:Mat m} (ht:T.IsHermitian)
    (hx:X.IsHermitian) (ha:A.IsHermitian) :
    Pj T X A=trN (X*A*T) := by
  have h : trN (A*X*T)= trN (X*A*T) := by
    rw [← trace_star_r]
    simp only [star_mul,(show star X=X from hx),(show star T=T from ht),
      (show star A=A from ha)]
    rw [trN_cyclic T]
  rw [Pj,jprod,mul_smul_comm,trN_smul,mul_add,trN_add,trN_cyclic T,trN_cyclic T,h]
  ring
lemma ipN_ent (A B:Mat m): ipN A B=mats (fun i=>∑ j,A i j*B i j) := by
  unfold ipN; rw [trace_pair]; congr 1
lemma ipN_comm (A B:Mat m): ipN A B=ipN B A := by rw [ipN_ent,ipN_ent]; simp_rw [mul_comm]
lemma young_H (X Y:Mat m) {d:ℝ} (hd:0<d) :
    -d*hsN X-ipN X Y ≤ (4*d)⁻¹*hsN Y := by
  rw [hsN_eq,hsN_eq,ipN_ent,mats_s2,mats_s2]
  have he (x y:ℝ) : -d*x^2-x*y ≤ (4*d)⁻¹*y^2 := by
    field_simp; nlinarith [sq_nonneg (2*d*x+y)]
  have hh :
      mats (fun i=> ∑ j, -d*X i j^2)≤ mats (fun i=>∑ j,(4*d)⁻¹*Y i j^2)+
        mats (fun i=>∑ j,X i j*Y i j) := by
    rw [← mats_add]
    apply mats_le; intro i; rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum
    intro j _; linarith [he (X i j) (Y i j)]
  linarith
lemma hsN_mul_bdd (T V:Mat m) (ht:T.IsHermitian) (hv:V.IsHermitian)
    (c:ℝ) (he:‖V‖≤c) : hsN (T*V) ≤ c^2 * trN (T*T) := by
  have hi : 0≤c := (norm_nonneg _).trans he
  have hh : V*V ≤ scalar m (c^2) := by
    apply (op_order_iff (sqPSD hv).posSemidef.1 (scalar_sym ..)).mpr; intro x
    rw [_root_.map_mul,_root_.mul_apply_eq_comp,← op_iff_hermitian.mp hv,
      real_inner_self_eq_norm_sq, op_scalar,real_inner_smul_right,real_inner_self_eq_norm_sq]
    rw [← mul_pow]
    have he' := ((op V).le_opNorm x).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    gcongr
  have h := trN_mul_mono hh (sqPSD ht)
  unfold hsN
  rw [star_mul,(show star T=T from ht),(show star V=V from hv)]
  calc
    _ = trN ((V*V)*(T*T)) := by
      rw [mul_assoc,trN_cyclic T]
      simp only [mul_assoc]
    _ ≤ _ := h
    _ = _ := by simp only [scalar,smul_mul_assoc,one_mul,trN_smul]

-- logarithm bound by derivative sign
lemma log_low (x:ℝ) (hx:tmin≤x):
    x- Real.log (1+x) ≤ x^2/(2*(1+tmin)) := by
  have hp : 0<1+tmin := by norm_num [tmin]
  let f := fun x:ℝ=> x-Real.log (1+x)-x^2/(2*(1+tmin))
  have hd (y:ℝ) (hy:tmin≤y) :
      HasDerivAt f (y*(tmin-y)/((1+tmin)*(1+y))) y := by
    have hi : 0<1+y := by linarith
    convert (((hasDerivAt_id' y).sub (((hasDerivAt_id' y).const_add 1).log hi.ne')).sub
      (((hasDerivAt_id' y).pow 2).div_const (2*(1+tmin)))) using 1
    all_goals first | rfl | (norm_num; field_simp; ring)
  have ht : tmin≤0 := by norm_num [tmin]
  have he : f 0=0 := by simp [f]
  suffices h:f x≤f 0 by rw [he] at h; exact sub_nonpos.mp h
  rcases le_total x 0 with hr|h
  · have h (y:ℝ) (hy:y∈Icc tmin 0) := hd y hy.1
    apply monotoneOn_of_deriv_nonneg (convex_Icc tmin 0)
      (fun x hx => (h x hx).continuousAt.continuousWithinAt) _ _ (show x∈Icc tmin 0 from ⟨hx,hr⟩)
      (show 0∈Icc tmin 0 from ⟨ht,le_rfl⟩)
    all_goals first | assumption | skip
    all_goals intro y hy; have hv : y∈Icc tmin 0 := interior_subset hy
    · exact (h y hv).differentiableAt.differentiableWithinAt
    rw [(h _ hv).deriv]
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hv.2 (sub_nonpos.mpr hv.1)) (by
      have hh : 0 < 1+y := by linarith [hv.1]
      positivity)
  have ih (y:ℝ) (hy:y∈Ici 0) := hd y (ht.trans hy)
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun y hy=>(ih y hy).continuousAt.continuousWithinAt) _ _ (show (0:ℝ)∈Ici 0 from mem_Ici.mpr le_rfl) h h
  all_goals intro y hy; have hv : y∈Ici 0 := interior_subset hy
  · exact (ih y hv).differentiableAt.differentiableWithinAt
  rw [(ih y hv).deriv]; change 0≤y at hv
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv (by linarith)) (by positivity)
lemma logSigma {T:Mat m} (h:T∈specBox m tmin tmax):
    trN T-logD (1+T) ≤ trN (T*T)/(2*(1+tmin)) := by
  have he := form_posDef (by norm_num) (add_cov_box h)
  rw [← trN_logD_eq he]
  let u:= Frm.eu h.1
  let l := u.eig T
  let A := diagonal l
  have ha : u.loc T=A := Frm.eu_d h.1
  have h₁ : u.loc (1+T)=diagonal (fun i=>1+l i) := by
    rw [Frm.loc_add,Frm.loc_one,ha]; unfold A; ext i j
    by_cases ht:i=j
    · subst j; simp
    simp [ht]
  have hd : u.Dgn (1+T) := by rw [Frm.Dgn,Frm.eig,h₁,Matrix.diag_diagonal]
  rw [← Frm.trNL u T,← Frm.trNL u (cfc Real.log _),← Frm.trNL u (T*T), Frm.loc_cfc
    _ he.1 hd, Frm.eig, h₁,Matrix.diag_diagonal,Frm.loc_mul,ha]
  unfold A trN trace
  simp only [Matrix.diagonal_mul_diagonal,Matrix.diag_diagonal,← sub_div,
    ← Finset.sum_sub_distrib]
  have hp (i:Fin m): tmin≤l i := by
    apply (spectrum_order T h.1 (l:=tmin) (r:=tmax)).1.mp h.2.1
    rw [h.1.spectrum_real_eq_range_eigenvalues]; unfold l u; rw [Frm.eu_eig]; exact ⟨_,rfl⟩
  rw [div_right_comm]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (g:=fun i=> l i^2/(2*(1+tmin))) (f:=fun i=>l i-Real.log (1+l i))
    (fun i _=> log_low (l i) (hp i))
  rw [← Finset.sum_div] at hh
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa [pow_two] using hh

namespace ProjField
variable [NeZero m] (q:ProjField m)
lemma residual_odd (T:Mat m) (hh:q.avgA=0) :
    Pt T q.RR (q.FL.eval (deriv v)) =
      Pt T q.Ro (q.FL.eval (fun x=>deriv v x-x)) := by
  let f := fun x:ℝ=>deriv v x-x
  let g := deriv v
  let W := q.FL
  have hg := v_test.der
  have hf := hg.sub TestF.id
  have he : W.eval f = fun x=> W.eval g x-q.Lmat x := by ext x; rw [W.eval_sub hg TestF.id,q.evId]
  have ha : HasSum (CpPair T q.RR (W.eval g)) _ := pt_sum q.R_reg (W.eval_reg hg)
  have hb := pt_sum (B:=T) q.Ro_reg (W.eval_reg hf)
  apply HasSum.unique ha
  convert hb using 1
  ext a
  unfold CpPair; rw [q.coRo,he,
    cof_subm (W.eval_reg hg) q.l_reg]
  split_ifs with ht
  · have hi := cof_odd_zero _ a ht (q.BoEval (map_deriv_even v_test Veven))
    rw [show cof (W.eval g) a=0 from hi]
    simp [Pj,jprod,trN]
  by_cases hx:deg a=1
  · rw [q.bal_cf hh a (by omega)]; simp [Pj,jprod,trN]
  rw [q.coL_o hx,sub_zero]

lemma RoH (x) : (q.Ro x).IsHermitian :=
  ((q.r_sym x).sub (q.r_sym (-x))).smul (by simp [IsSelfAdjoint])
lemma end_cost (T:Mat m) (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat)
    (hs:LayerOK) (h:q.avgA=0) :
    -eta*Pt q.covMat q.Ro q.Ro -Pt T q.RR (q.FL.eval (deriv v)) + (trN T-logD q.covMat) ≤
      18/10*trN (T*T) := by
  let b:ℝ:=319/1000
  let f := fun x=>deriv v x-x
  let g := q.FL.eval f
  let d:= eta*(1+tmin)
  have hf := q.FL.eval_reg (v_test.der.sub TestF.id)
  have hd : 0<d := by norm_num [d,eta,tmin]
  have hh(x) :
      -eta*Pj q.covMat (q.Ro x) (q.Ro x)-Pj T (q.Ro x) (g x) ≤
        (4*d)⁻¹*b^2 * trN (T*T) := by
    let V := g x
    let A := q.Ro x
    have hv : V.IsHermitian := cfc_herm ..
    have hA:= q.RoH x
    have ht' := ht.1
    have hi : ‖V‖≤ b := by
      have hi : IsSelfAdjoint (q.FL.A x):=q.FL.sym x
      apply norm_cfc_le (show 0≤b by norm_num [b])
      exact fun x _=> hs.v_bound x
    have hz : Pj T A V=ipN A (T*V) := by
      unfold ipN; rw [pj_cyc3 ht' hA hv,star_mul,show star V=_ from hv, show star T=_ from ht',mul_assoc]
    have hu : scalar m (1+tmin)≤q.covMat := by rw [← he,scalar, add_smul,one_smul]; exact add_le_add le_rfl ht.2.1
    have he := p_le_p hu hA
    have he' : Pj (scalar m (1+tmin)) A A=(1+tmin)*hsN A := by
      rw [Pj,j_same,scalar,smul_mul_assoc,one_mul,trN_smul,hsN,show star A=A from hA]
    rw [he'] at he
    have hp := hsN_mul_bdd T V ht' hv b hi
    change -eta*_ -Pj T A V ≤ _
    rw [hz]; have hh := young_H A (T*V) hd
    unfold d eta tmin at *; norm_num at *; linarith
  have HP := q.Ro_reg
  have hi := integral_mono (μ:=normal m)
    (show Integrable (fun x=> -eta*Pj q.covMat (q.Ro x) (q.Ro x)-Pj T (q.Ro x) (g x)) (normal m) from
      (((pj_poly_part HP _).const_mul _).sub (by
        simp_rw [← pJ_eq]; exact proj_int _ HP hf))) (integrable_const _) hh
  rw [integral_sub,integral_const_mul] at hi
  · rw [q.residual_odd T h,← he]
    have hv := logSigma ht
    have hq := (trN_mono (sqPSD ht.1))
    simp only [trN,trace_zero,zero_div] at hq
    simp only [integral_const,probReal_univ,one_smul] at hi
    change -eta*Pt q.covMat _ _-Pt T q.Ro g≤_ at hi
    rw [he] at *
    unfold b d eta tmin at *; norm_num at *
    change 0 ≤ trN (T*T) at hq; unfold g f at hi; linarith
  · exact (pj_poly_part HP _).const_mul _
  simp_rw [← pJ_eq]; exact proj_int _ HP hf
end ProjField
end GeneralMahler

end

end OAI

import OAI.Geometry.Convex.GeneralMahler.TraceOrder

namespace OAI
/-! Normalized log determinant; derivative and simple growth estimates. -/
noncomputable section
open Finset MeasureTheory Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m:ℕ}

def logD (A:Mat m) := Real.log A.det/(m:ℝ)
def coeffMap (i j:Fin m) : Mat m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun := fun A : Mat m => A i j
    map_add' := fun _ _=>rfl
    map_smul' := fun _ _=>rfl }

lemma det_cdiff : ContDiff ℝ ⊤ (Matrix.det (n:=Fin m) (R:=ℝ)) := by
  simp_rw [funext det_apply']
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  exact (coeffMap (σ i) i).contDiff

lemma D_log {A:Mat m} (h:A.PosDef) : ContDiffAt ℝ ⊤ logD A :=
  ((det_cdiff.contDiffAt.log h.det_pos.ne').div_const (m:ℝ))
lemma meas_logD : Measurable (@logD m) :=
  (Real.measurable_log.comp det_cdiff.continuous.measurable).div_const _

lemma perm_moves {σ:Equiv.Perm (Fin m)} (h:σ≠1) (i:Fin m) :
    ∃ j≠i,σ j≠j := by
  by_contra! H
  apply h
  ext j : 1
  change σ j=j
  by_contra hh
  have he : σ (σ j) = σ j := H _ (by
    have hi : j=i := by by_contra a; exact hh (H j a)
    rwa [← hi])
  exact hh (σ.injective he)
lemma det_at_I_curve {f:ℝ→Mat m} {B:Mat m} {x:ℝ} (he : f x=1) (h:HasDerivAt f B x) :
    HasDerivAt (fun t:ℝ=>Matrix.det (f t)) B.trace x := by
  classical
  let e (σ : Equiv.Perm (Fin m)) := (((Equiv.Perm.sign σ).val:ℤ):ℝ)
  have hi (σ:Equiv.Perm (Fin m)) :
      HasDerivAt (fun t => e σ * ∏ i, f t (σ i) i)
        (e σ * ∑ i, (∏ j∈(Finset.univ.erase i), f x (σ j) j) * B (σ i) i) x := by
    have hh (i : Fin m) : HasDerivAt (fun t:ℝ=> f t (σ i) i) (B (σ i) i) x :=
      (coeffMap (σ i) i).hasFDerivAt.comp_hasDerivAt x h
    exact (HasDerivAt.fun_finsetProd (u:=Finset.univ) fun i _=> hh i).const_mul _
  have hh := HasDerivAt.fun_sum (u:=Finset.univ) (fun σ _=>hi σ)
  simp_rw [he] at hh
  convert hh using 1
  all_goals first | rfl | (funext x; exact det_apply' _) | skip
  rw [Finset.sum_eq_single_of_mem (1:Equiv.Perm (Fin m)) (Finset.mem_univ _)]
  · simp [e,Matrix.trace,Matrix.one_apply]
  intro b hb he
  suffices h : (∑ i, (∏ j∈(Finset.univ.erase i), (1:Mat m) (b j) j)*B (b i) i)=0 by rw [h,mul_zero]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨j,hj,h⟩ := perm_moves he i
  rw [Finset.prod_eq_zero (f:=fun j=>(1:Mat m) (b j) j) (by simp [hj]) (show (1:Mat m) (b j) j=0 from by simp [h]),zero_mul]

lemma deriv_logD {f:ℝ→Mat m} {B:Mat m} {x:ℝ} (h:HasDerivAt f B x) (hh:(f x).PosDef) :
    HasDerivAt (fun t=>logD (f t)) (trN ((f x)⁻¹ * B)) x := by
  let g := fun t => (f x)⁻¹ * f t
  have hi : HasDerivAt g ((f x)⁻¹ * B) x := h.const_mul _
  have he := det_at_I_curve (show g x=1 from inv_mul' hh) hi
  have heq : (fun t=> Matrix.det (f t)) = fun t=> Matrix.det (f x)* Matrix.det (g t) := by
    ext t
    rw [← Matrix.det_mul,show f x*g t=f t from by unfold g; rw [← mul_assoc,mul_inv' hh,one_mul]]
  have hf := he.const_mul (Matrix.det (f x))
  rw [← heq] at hf
  convert (hf.log hh.det_pos.ne').div_const (m:ℝ) using 1
  all_goals first | rfl | (simp only [trN]; field_simp [hh.det_pos.ne'])

lemma logD_sum {A:Mat m} (ha:A.PosDef) :
    logD A=(∑ i,Real.log (ha.1.eigenvalues i))/(m:ℝ) := by
  rw [logD,ha.1.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [Real.log_prod (fun i _=>?_)]
  exact ne_of_gt (ha.eigenvalues_pos i)

lemma logD_between {A:Mat m} [NeZero m] (ha:A.PosDef) {a:ℝ}
    (h:0<a) (hh:scalar m a ≤ A) :
    Real.log a ≤ logD A ∧ logD A ≤ trN A := by
  rw [logD_sum ha,trN,ha.1.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  constructor
  · rw [le_div_iff₀ ProjField.m_pos]
    have he (i) : Real.log a ≤ Real.log (ha.1.eigenvalues i) := by
      apply Real.log_le_log h
      apply (spectrum_order A ha.1 (l:=a) (r:=a)).1.mp hh
      rw [ha.1.spectrum_real_eq_range_eigenvalues]
      exact ⟨i,rfl⟩
    apply le_trans _ (Finset.sum_le_sum (fun i _=>he i))
    simp; rw [mul_comm]
  gcongr
  have hx := Real.log_le_sub_one_of_pos (ha.eigenvalues_pos i)
  linarith

lemma logD_scalar [NeZero m] {c:ℝ} : logD (scalar m c)=Real.log c := by
  rw [logD,scalar,det_smul, det_one,mul_one,Real.log_pow]
  simp; have h:= ProjField.m_pos (m:=m); field_simp

-- trace comparison for final connection
lemma trN_logD_eq {A:Mat m} (ha:A.PosDef) :
    trN (cfc Real.log A)=logD A := by
  rw [trN,logD_sum ha]
  open Unitary in
    rw [Matrix.IsHermitian.cfc_eq ha.1,Matrix.IsHermitian.cfc,conjStarAlgAut_apply,
      Matrix.trace_mul_comm,← mul_assoc]
    simp

end GeneralMahler

end

end OAI

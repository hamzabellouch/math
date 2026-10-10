import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Pack
import OAI.Analysis.MatrixSigning.Optimization.InverseEliminationBounds

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

private local instance : NormedAddCommGroup (PairHilbert d) := inferInstance
private local instance : NormedSpace ℝ (PairHilbert d) := inferInstance
private local instance : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace

private local instance : NormedAddCommGroup (Vars d) := inferInstance
private local instance : NormedSpace ℝ (Vars d) := inferInstance
private local instance : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

lemma norm_one_sq : ‖(Hermitian.one : H d)‖^2 = (d : ℝ) := by
  rw [← real_inner_self_eq_norm_sq,inner_one,realTrace_one]

lemma identityPair_norm_sq : ‖identityPair d‖^2 = 2*(d : ℝ) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(Hermitian.one : H d)‖^2+‖(Hermitian.one : H d)‖^2 = _
  rw [norm_one_sq]
  ring

lemma norm_sq_le_trace_of_psd_le_one (P : H d) (hP : P ∈ psdCone d) (hPle : P ≤ Hermitian.one) :
    ‖P‖^2 ≤ realTrace P := by
  have hh := inner_nonneg_of_psd P (Hermitian.one-P) hP
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hPle))
  rw [inner_sub_right,inner_one',real_inner_self_eq_norm_sq] at hh
  linarith

lemma trace_pair_norm (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (htr : realTrace P+realTrace Q=1) :
    P ≤ Hermitian.one ∧ Q ≤ Hermitian.one ∧
    ‖(pairEquiv d).symm (P,Q)‖ ≤ 1 ∧
    1 ≤ 2*(d : ℝ)*‖(pairEquiv d).symm (P,Q)‖^2 := by
  have hPn := realTrace_nonneg hP
  have hQn := realTrace_nonneg hQ
  have hPle : P ≤ Hermitian.one := (trace_bound_above hP).trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show realTrace P ≤ 1 by linarith))
  have hQle : Q ≤ Hermitian.one := (trace_bound_above hQ).trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show realTrace Q ≤ 1 by linarith))
  have hn2 : ‖(pairEquiv d).symm (P,Q)‖^2 ≤ 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖P‖^2+‖Q‖^2 ≤ 1
    have h₁ := norm_sq_le_trace_of_psd_le_one P hP hPle
    have h₂ := norm_sq_le_trace_of_psd_le_one Q hQ hQle
    linarith
  have hi : inner ℝ (identityPair d) ((pairEquiv d).symm (P,Q)) = 1 := by
    change inner ℝ (Hermitian.one : H d) P+inner ℝ (Hermitian.one : H d) Q = 1
    rwa [inner_one,inner_one]
  have hc := abs_real_inner_le_norm (identityPair d) ((pairEquiv d).symm (P,Q))
  rw [hi,abs_one] at hc
  have hc2 := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hc 2
  rw [mul_pow,identityPair_norm_sq,one_pow] at hc2
  refine ⟨hPle,hQle,?_,hc2⟩
  nlinarith [norm_nonneg ((pairEquiv d).symm (P,Q))]

theorem full_jacobian_inverse_bound [NeZero d] (X Y P Q : H d)
    (η : H d →L[ℝ] H d) (hηpos : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hηsym : SymmetricMap η) (hX : X ∈ pd d) (hY : Y ∈ pd d)
    (hP : P ∈ pd d) (hQ : Q ∈ pd d) {ε : ℝ} (hε : 0 < ε)
    (htr : realTrace P+realTrace Q=1)
    (hStatX : sandwich (invH X) P = η Q+ε • (Hermitian.one : H d))
    (hStatY : sandwich (invH Y) Q = η P+ε • (Hermitian.one : H d))
    (hXlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ X)
    (hYlo : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ Y)
    (hXhi : X ≤ (100/ε) • (Hermitian.one : H d))
    (hYhi : Y ≤ (100/ε) • (Hermitian.one : H d)) :
    ∃ J : Vars d ≃L[ℝ] Vars d,
      (∀ v,J v = CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint X Y η)) (hessian X Y P Q) v) ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*((d : ℝ)+1)*(1+ε⁻¹)^4 := by
  have hPX : P = sandwich X (η Q)+ε • sandwich X (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hStatX,sandwich_inverse_cancel _ _ hX]
  have hQY : Q = sandwich Y (η P)+ε • sandwich Y (Hermitian.one : H d) := by
    rw [← sandwich_smul,← sandwich_add,← hStatY,sandwich_inverse_cancel _ _ hY]
  obtain ⟨V,hV,hVpos⟩ := linConstraint_positive_inverse X Y P Q η hηpos hX hY hP hQ hε hPX hQY
  let L : PairHilbert d ≃L[ℝ] PairHilbert d := ((pairEquiv d).trans V).trans (pairEquiv d).symm
  have he : L.toContinuousLinearMap = onPairHilbert (linConstraint X Y η) := by
    apply ContinuousLinearMap.ext
    intro u
    change (pairEquiv d).symm (V (pairEquiv d u)) =
      (pairEquiv d).symm (linConstraint X Y η (pairEquiv d u))
    rw [hV]
  have hs := CurrentKS.KKT.equiv_symmetric_of_map_eq L _ he
    (linConstraint_symmetric X Y η hηsym)
  obtain ⟨J,hJ⟩ := CurrentKS.KKT.exists_jacobian_equiv (identityPair d)
    identityPair_ne_zero L hs (hessian X Y P Q) (hessian_strict_pos X Y P Q hX hY hP hQ)
  refine ⟨J, fun v => ?_, ?_⟩
  · exact (hJ v).trans (congrArg (fun T =>
      CurrentKS.KKT.jacobian (identityPair d) T (hessian X Y P Q) v) he)
  obtain ⟨hPle,hQle,hnorm,hbelow⟩ := trace_pair_norm P Q hP.posSemidef hQ.posSemidef htr
  have hB : ‖L.symm.toContinuousLinearMap‖ ≤ ε⁻¹ :=
    linConstraint_inverse_norm X Y P Q η hηsym hε hPle hQle hStatX hStatY V hV hVpos
  have hLe : L ((pairEquiv d).symm (P,Q)) = ε • identityPair d := by
    change (pairEquiv d).symm (V ((pairEquiv d) ((pairEquiv d).symm (P,Q)))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,hV,linConstraint_stationary X Y P Q η ε hStatX hStatY]
    exact (map_smul (pairEquiv d).symm ε _)
  have hiE : L.symm (identityPair d) = ε⁻¹ • (pairEquiv d).symm (P,Q) := by
    apply L.injective
    rw [L.apply_symm_apply,map_smul,hLe,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
  have hnE : ‖L.symm (identityPair d)‖ = ε⁻¹*‖(pairEquiv d).symm (P,Q)‖ := by
    rw [hiE,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
  have hBe : ‖L.symm (identityPair d)‖ ≤ ε⁻¹ := by
    rw [hnE]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hε.le)
  have hεX : ε • (Hermitian.one : H d) ≤ sandwich (invH X) P := by
    rw [hStatX]
    exact le_add_of_nonneg_left (psd_nonneg (hηpos _ hQ.posSemidef))
  have hεY : ε • (Hermitian.one : H d) ≤ sandwich (invH Y) Q := by
    rw [hStatY]
    exact le_add_of_nonneg_left (psd_nonneg (hηpos _ hP.posSemidef))
  have hess := hessian_bounds X Y P Q hX hY hε (show (0:ℝ)<100 by norm_num)
    (by convert hXlo using 1; norm_num) (by convert hYlo using 1; norm_num)
    hXhi hYhi hPle hQle hεX hεY
  have hd : (0:ℝ)<d := by exact_mod_cast NeZero.pos d
  have hden : 1/(100*(d : ℝ)) ≤ inner ℝ (L.symm (identityPair d))
      (hessian X Y P Q (L.symm (identityPair d))) := by
    apply le_trans _ (hess.1 _)
    rw [hnE]
    have heq : (2*ε^2/100)*(ε⁻¹*‖(pairEquiv d).symm (P,Q)‖)^2 =
        (2/100 : ℝ)*‖(pairEquiv d).symm (P,Q)‖^2 := by field_simp [hε.ne']
    rw [heq]
    apply (div_le_iff₀ (show (0:ℝ)<100*d by positivity)).mpr
    nlinarith only [hbelow]
  apply CurrentKS.KKT.jacobian_inverse_norm_100 (identityPair d) L hs (hessian X Y P Q) J hJ
    hε hd hB hBe _ hden
  convert hess.2 using 1
  norm_num

end
end CurrentKS.Variational

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.InverseProfile

namespace OAI

section

noncomputable section
open Set
open scoped Topology

namespace WeakMTWTransport
section PullbackDet
variable {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace E] [CompleteSpace F]

lemma abs_det_hessian_pullback (B:E →L[ℝ] F) (W:F →L[ℝ] F)
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) :
    |(B.adjoint.comp (W.comp B)).det|=B.toLinearMap.normDet^2*|W.det| := by
  have h1:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap W.toLinearMap hd
  have h2:=LinearMap.normDet_comp_of_finrank_eq (W.comp B).toLinearMap B.adjoint.toLinearMap hd
  have h3:=LinearMap.normDet_comp_of_finrank_eq B.toLinearMap B.adjoint.toLinearMap hd
  have hs:(B.adjoint.comp B).det=B.toLinearMap.normDet^2:=by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using B.normDet_sq.symm
  rw [LinearMap.normDet_eq_abs_det] at h2 h3
  change |(B.adjoint.comp B).det|=B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet at h3
  rw [hs,abs_of_nonneg (sq_nonneg _)] at h3
  rw [LinearMap.normDet_eq_abs_det] at h1
  change |(B.adjoint.comp (W.comp B)).det|=_ at h2
  rw [h2]
  change B.adjoint.toLinearMap.normDet*(W.comp B).toLinearMap.normDet=_
  rw [show (W.comp B).toLinearMap.normDet=|W.det| *B.toLinearMap.normDet from h1]
  calc
    _ = (B.adjoint.toLinearMap.normDet*B.toLinearMap.normDet)*|W.det| := by ring
    _ = _ := by rw [←h3]

omit [CompleteSpace E] in
lemma symmetric_det_pos {A:E →L[ℝ] E}
    (hA:∀x y,inner ℝ (A x) y=inner ℝ x (A y))
    (hp:∀x,x≠0 → 0 < inner ℝ (A x) x) : 0<A.det := by
  have hs:A.toLinearMap.IsSymmetric:=hA
  change 0<A.toLinearMap.det
  rw [hs.det_eq_prod_eigenvalues rfl]
  exact Finset.prod_pos (fun i _=>symmetric_eigenvalue_pos hs rfl hp i)

lemma det_positive_hessian_pullback {B:E →L[ℝ] F} {W:F →L[ℝ] F}
    (hd:Module.finrank ℝ E=Module.finrank ℝ F) (hi:Function.Injective B)
    (hW:∀x y,inner ℝ (W x) y=inner ℝ x (W y))
    (hp:∀x,x≠0 → 0 < inner ℝ (W x) x) {l:ℝ} (hl:0<l) :
    (∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d) ∧
    (l • (B.adjoint.comp (W.comp B))).det=
      l^Module.finrank ℝ E*B.toLinearMap.normDet^2*W.det := by
  have hs:∀x y,inner ℝ ((l • (B.adjoint.comp (W.comp B))) x) y=
      inner ℝ x ((l • (B.adjoint.comp (W.comp B))) y):=by
    intro x y
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right,hW]
  have hpos:∀d,d≠0 → 0 < inner ℝ ((l • (B.adjoint.comp (W.comp B))) d) d := by
    intro d hd
    simp only [smul_apply,ContinuousLinearMap.comp_apply,
      real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    exact mul_pos hl (hp _ (fun h=>hd (hi (h.trans B.map_zero.symm))))
  refine ⟨hpos,?_⟩
  have H:=abs_det_hessian_pullback B W hd
  have hpull:0<(B.adjoint.comp (W.comp B)).det:=by
    apply symmetric_det_pos
    · intro x y
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_right,hW]
    · intro d hd
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]
      exact hp _ (fun h=>hd (hi (h.trans B.map_zero.symm)))
  rw [abs_of_pos hpull,abs_of_pos (symmetric_det_pos hW hp)] at H
  change (l • (B.adjoint.comp (W.comp B)).toLinearMap).det=_
  rw [LinearMap.det_smul]
  change l^Module.finrank ℝ E*(B.adjoint.comp (W.comp B)).det=_
  rw [H]
  ring
end PullbackDet
end WeakMTWTransport

end
end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondFderivScalarComp
import OAI.Analysis.BiholderTransport.Coordinates.ScalarExpansion

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma quadraticTaylor_hasFDerivAt (f0:ℝ) (p:E) {A:E →L[ℝ] E}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e)) (x:E) :
    HasFDerivAt (quadraticTaylor f0 p A) (innerSL ℝ (p+A x)) x := by
  have H:=((hasFDerivAt_const f0 x).add ((innerSL ℝ p).hasFDerivAt)).add
    ((A.hasFDerivAt.inner ℝ (hasFDerivAt_id x)).const_smul (1/2:ℝ))
  convert! H using 1
  · funext d
    simp only [quadraticTaylor, Pi.add_apply, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul, id_eq]
    ring
  · ext d
    simp only [add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,
      fderivInnerCLM_apply,inner_add_left,zero_add,smul_eq_mul, id_eq]
    rw [hA d x,real_inner_comm d (A x)]
    ring

omit [CompleteSpace E] in
lemma quadraticTaylor_second_fderiv (f0:ℝ) (p:E) {A:E →L[ℝ] E}
    (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e)) (x:E) :
    fderiv ℝ (fderiv ℝ (quadraticTaylor f0 p A)) x=(innerSL ℝ).comp A := by
  have he:fderiv ℝ (quadraticTaylor f0 p A)=(fun x=>innerSL ℝ (p+A x)):= by
    funext x
    exact (quadraticTaylor_hasFDerivAt f0 p hA x).fderiv
  rw [he]
  have H:=((innerSL ℝ).hasFDerivAt).comp x ((hasFDerivAt_const p x).add A.hasFDerivAt)
  simpa only [zero_add,Function.comp_def,Pi.add_apply] using H.fderiv

lemma quadratic_expansion_scalar_formula [FiniteDimensional ℝ E] {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) (hA:∀d e,inner ℝ (A d) e=inner ℝ d (A e))
    {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (f 0)) :
    ∃q:E,∃B:E →L[ℝ] E,(∀d e,inner ℝ (B d) e=inner ℝ d (B e)) ∧
      HasQuadraticExpansion (fun h=>φ (f h)) q B ∧
      ∀d,inner ℝ (B d) d=iteratedDeriv 2 φ (f 0)*(inner ℝ p d)^2+
        deriv φ (f 0)*inner ℝ (A d) d := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P := by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hp0:P 0=f 0 := by simp only [P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  have hQ:ContDiffAt ℝ 2 (fun h=>φ (P h)) 0 := (hp0.symm ▸ hφ).comp 0 hP.contDiffAt
  have H:=quadratic_expansion_scalar_proxy hf hφ
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun h=>φ (P h)) 0),
    bilinearOperator (fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0),?_,?_,?_⟩
  · intro d e
    rw [bilinearOperator_inner]
    calc
      _ = fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0 e d :=
        (hQ.isSymmSndFDerivAt (by norm_num)).eq d e
      _ = _ := by rw [real_inner_comm,bilinearOperator_inner]
  · intro epsilon hepsilon
    obtain ⟨radius,hradius,hball⟩ := Metric.eventually_nhds_iff.mp (H.eventually hepsilon)
    refine ⟨radius,hradius,?_⟩
    intro vector hvector
    have hbound := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hvector)
    simpa only [P,quadraticTaylor,bilinearOperator_inner,InnerProductSpace.toDual_symm_apply,
      sub_add_eq_sub_sub] using hbound
  · intro d
    rw [bilinearOperator_inner,second_fderiv_scalar_comp hP.contDiffAt (hp0.symm ▸ hφ),hp0]
    rw [show fderiv ℝ P 0=innerSL ℝ p from by
      simpa only [map_zero,add_zero] using (quadraticTaylor_hasFDerivAt (f 0) p hA 0).fderiv]
    rw [quadraticTaylor_second_fderiv (f 0) p hA]
    rfl
end WeakMTWTransport

end

end OAI

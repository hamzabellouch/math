import Mathlib
import OAI.Analysis.BiholderTransport.Contact.Subgradient
import OAI.Analysis.BiholderTransport.Calculus.FullSet
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder

namespace OAI

noncomputable section
open Set Filter Asymptotics
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma quadratic_expansion_polynomial_remainder {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) :
    (fun h=>f h-quadraticTaylor (f 0) p A h)=o[𝓝 0] (fun h:E=>‖h‖^2) := by
  apply IsLittleO.of_bound
  intro ε hε
  obtain ⟨r,hr,H⟩:=hf ε hε
  filter_upwards [Metric.ball_mem_nhds (0:E) hr] with h hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
    H h (by simpa only [Metric.mem_ball,dist_zero_right] using hh)

omit [CompleteSpace E] in
lemma HasSecondTaylor.of_littleO_difference {f g:E → ℝ}
    {l:E →L[ℝ] ℝ} {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hg:HasSecondTaylor g l B) (h0:f 0=g 0)
    (hfg:(fun h=>f h-g h)=o[𝓝 0] (fun h:E=>‖h‖^2)) : HasSecondTaylor f l B := by
  unfold HasSecondTaylor at hg ⊢
  convert! hfg.add hg using 1
  funext h
  rw [h0]
  ring

omit [CompleteSpace E] in
lemma quadratic_expansion_scalar_proxy {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (f 0)) :
    let P:=quadraticTaylor (f 0) p A
    HasSecondTaylor (fun h=>φ (f h)) (fderiv ℝ (fun h=>φ (P h)) 0)
      (fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0) := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P := by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hp0:P 0=f 0 := by simp only [P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  have hQ:ContDiffAt ℝ 2 (fun h=>φ (P h)) 0 := (hp0.symm ▸ hφ).comp 0 hP.contDiffAt
  apply (hasSecondTaylor_of_contDiffAt hQ).of_littleO_difference
  · simp only [hp0]
  · obtain ⟨K,s,hs,hK⟩:=(hφ.of_le (by norm_num : (1:WithTop ℕ∞)≤2)).exists_lipschitzOnWith
    have hpc:Tendsto P (𝓝 0) (𝓝 (f 0)) := hp0 ▸ hP.continuous.continuousAt.tendsto
    have hrem:Tendsto (fun vector => f vector-P vector) (𝓝 0) (𝓝 0) :=
      (quadratic_expansion_polynomial_remainder hf).trans_tendsto (by
        simpa using (continuous_norm.tendsto (0:E)).pow 2)
    have hfc:ContinuousAt f 0 := by
      change Tendsto f (𝓝 0) (𝓝 (f 0))
      simpa only [sub_add_cancel,zero_add] using hrem.add hpc
    have H:(fun h=>φ (f h)-φ (P h))=O[𝓝 0] (fun h=>f h-P h) := by
      apply IsBigO.of_bound (K:ℝ)
      filter_upwards [hfc hs,hpc hs] with h hf hs
      simpa only [dist_eq_norm] using hK.dist_le_mul (f h) hf (P h) hs
    exact H.trans_isLittleO (quadratic_expansion_polynomial_remainder hf)

lemma quadratic_expansion_scalar_exists [FiniteDimensional ℝ E] {f:E → ℝ} {p:E} {A:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) {φ:ℝ → ℝ} (hφ:ContDiffAt ℝ 2 φ (f 0)) :
    ∃q:E,∃B:E →L[ℝ] E,(∀d e,inner ℝ (B d) e=inner ℝ d (B e)) ∧
      HasQuadraticExpansion (fun h=>φ (f h)) q B := by
  let P:=quadraticTaylor (f 0) p A
  have hP:ContDiff ℝ 2 P := by
    dsimp only [P,quadraticTaylor]
    exact (contDiff_const.add (contDiff_const.inner ℝ contDiff_id)).add
      ((A.contDiff.inner ℝ contDiff_id).div_const 2)
  have hp0:P 0=f 0 := by simp only [P,quadraticTaylor,map_zero,inner_zero_right,zero_div,add_zero]
  have hQ:ContDiffAt ℝ 2 (fun h=>φ (P h)) 0 := (hp0.symm ▸ hφ).comp 0 hP.contDiffAt
  have H:=quadratic_expansion_scalar_proxy hf hφ
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun h=>φ (P h)) 0),
    bilinearOperator (fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0),?_,?_⟩
  · intro first second
    rw [bilinearOperator_inner]
    calc
      _ = fderiv ℝ (fderiv ℝ (fun h=>φ (P h))) 0 second first :=
        (hQ.isSymmSndFDerivAt (by norm_num)).eq first second
      _ = _ := by rw [real_inner_comm,bilinearOperator_inner]
  · intro epsilon hepsilon
    obtain ⟨radius,hradius,hball⟩ := Metric.eventually_nhds_iff.mp (H.eventually hepsilon)
    refine ⟨radius,hradius,?_⟩
    intro vector hvector
    have hbound := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hvector)
    simpa only [P,quadraticTaylor,bilinearOperator_inner,InnerProductSpace.toDual_symm_apply,
      sub_add_eq_sub_sub] using hbound
end WeakMTWTransport

end

end OAI

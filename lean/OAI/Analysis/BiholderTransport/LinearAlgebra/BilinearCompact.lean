import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section BilinearCompact
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma symmetric_bilinear_norm_bound {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:∀d e,B d e=B e d) {C:ℝ} (hC:0≤C)
    (hbound:∀d,|B d d|≤C*‖d‖^2) : ‖B‖≤C := by
  let T:=bilinearOperator B
  have hT:T.IsSymmetric := bilinearOperator_symmetric hB
  have hn:‖T‖≤C := by
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro d
    by_cases hd:d=0
    · simpa [hd,ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hC
    · have hp:0<‖d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [T,bilinearOperator_inner,RCLike.re_to_real]
      rw [abs_div,abs_of_pos hp]
      apply (div_le_iff₀ hp).mpr
      exact hbound d
  apply B.opNorm_le_bound hC
  intro d
  apply (B d).opNorm_le_bound (mul_nonneg hC (norm_nonneg d))
  intro e
  calc
    ‖B d e‖ = ‖inner ℝ (T d) e‖ := by simp only [T,bilinearOperator_inner]
    _ ≤ ‖T d‖*‖e‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖*‖d‖)*‖e‖ := mul_le_mul_of_nonneg_right (T.le_opNorm d) (norm_nonneg e)
    _ ≤ (C*‖d‖)*‖e‖ := by gcongr

lemma symmetric_bilinear_norm_of_two_bounds {B:E →L[ℝ] E →L[ℝ] ℝ}
    (hB:∀d e,B d e=B e d) {C D:ℝ} (hC:0≤C) (hD:0≤D)
    (hlo:∀d,-C*‖d‖^2≤B d d) (hhi:∀d,B d d≤D*‖d‖^2) : ‖B‖≤C+D := by
  apply symmetric_bilinear_norm_bound hB (add_nonneg hC hD)
  intro d
  rw [abs_le]
  constructor
  · nlinarith only [hlo d,mul_nonneg hD (sq_nonneg ‖d‖)]
  · nlinarith only [hhi d,mul_nonneg hC (sq_nonneg ‖d‖)]

omit [CompleteSpace E] in
lemma rough_hessian_symmetric {f:E → ℝ} {x:E}
    (hnear:∀ᶠ z in 𝓝 x,DifferentiableAt ℝ f z)
    (hf:DifferentiableAt ℝ (fderiv ℝ f) x) :
    ∀d e,fderiv ℝ (fderiv ℝ f) x d e=fderiv ℝ (fderiv ℝ f) x e d :=
  second_derivative_symmetric_of_eventually (hnear.mono (fun _ h=>h.hasFDerivAt)) hf.hasFDerivAt

local instance bilinearCompactDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance bilinearCompactDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance bilinearCompactGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance bilinearCompactSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [CompleteSpace E] in
lemma exists_bilinear_limit [FiniteDimensional ℝ E]
    {Bj:ℕ → E →L[ℝ] E →L[ℝ] ℝ} {C:ℝ}
    (hb:∀ᶠ j in atTop,‖Bj j‖≤C) :
    ∃B:E →L[ℝ] E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧ Tendsto (Bj ∘ σ) atTop (𝓝 B) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  have H : IsCompact (Metric.closedBall (0:E →L[ℝ] E →L[ℝ] ℝ) C) := isCompact_closedBall _ _
  obtain ⟨B,hB,σ,hσ,hlim⟩:=H.tendsto_subseq (x := fun j => Bj (j+N)) (fun j=>by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hN (j+N) (Nat.le_add_left _ _))
  exact ⟨B,fun j=>σ j+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,hlim⟩
end BilinearCompact
end WeakMTWTransport

end
end

end OAI

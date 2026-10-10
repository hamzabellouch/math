import OAI.Analysis.KadisonKastler.CentralDefectMultiplication
import OAI.Analysis.KadisonKastler.BoundedSequence

namespace OAI

/-! # The C-star algebra of asymptotically central bounded sequences

The centrality defect is measured on the standard reference vector.
Its product estimate and adjoint symmetry give the sequence algebra
used in the bicentralizer argument (Haagerup, Acta Math.158(1987), §1).
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def AsymptoticallyCentral (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    (x : BoundedSequence (Algebra M)) : Prop :=
  Tendsto (fun n => ‖centralVectorDefect J ξ (x n).val‖) atTop (𝓝 0)

theorem AsymptoticallyCentral.add {J : H ≃ₗᵢ⋆[ℂ] H} {ξ : H}
    {x y : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x)
    (hy : AsymptoticallyCentral J ξ y) : AsymptoticallyCentral J ξ (x+y) := by
  change Tendsto (fun n => ‖centralVectorDefect J ξ ((x n).val + (y n).val)‖) atTop (𝓝 0)
  simp only [map_add]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_add_le (centralVectorDefect J ξ (x n).val) (centralVectorDefect J ξ (y n).val))
  simpa only [add_zero] using Filter.Tendsto.add hx hy

theorem AsymptoticallyCentral.smul {J : H ≃ₗᵢ⋆[ℂ] H} {ξ : H}
    {x : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x) (c : ℂ) :
    AsymptoticallyCentral J ξ (c • x) := by
  change Tendsto (fun n => ‖centralVectorDefect J ξ (c • (x n).val)‖) atTop (𝓝 0)
  simp only [map_smul,norm_smul]
  simpa only [mul_zero] using hx.const_mul ‖c‖

theorem AsymptoticallyCentral.star
    {J : H ≃ₗᵢ⋆[ℂ] H} (hJ : Function.Involutive J) {ξ : H} (hξ : J ξ = ξ)
    {x : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x) :
    AsymptoticallyCentral J ξ (star x) := by
  change Tendsto (fun n => ‖centralVectorDefect J ξ (Star.star (x n).val)‖) atTop (𝓝 0)
  simpa only [AsymptoticallyCentral,centralVectorDefect_star_norm J hJ ξ hξ] using hx

theorem AsymptoticallyCentral.mul
    {J : H ≃ₗᵢ⋆[ℂ] H} (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant) {ξ : H}
    {x y : BoundedSequence (Algebra M)} (hx : AsymptoticallyCentral J ξ x)
    (hy : AsymptoticallyCentral J ξ y) : AsymptoticallyCentral J ξ (x*y) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (centralVectorDefect_mul_norm_le J hJ hright ξ (x n) (y n)).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right (x.norm_coe_le_norm n) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (y.norm_coe_le_norm n) (norm_nonneg _))))
  simpa only [mul_zero,add_zero] using (hy.const_mul ‖x‖).add (hx.const_mul ‖y‖)

theorem asymptoticallyCentral_isClosed (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) : IsClosed {x : BoundedSequence (Algebra M) | AsymptoticallyCentral J ξ x} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := 2 * ‖ξ‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hden : 0 < 2 * (C+1) := by positivity
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx (ε / (2*(C+1))) (div_pos hε hden)
  have hnxy : ‖x-y‖ < ε / (2*(C+1)) := by simpa only [dist_eq_norm] using hxy
  filter_upwards [(Metric.tendsto_nhds.mp hy) (ε/2) (half_pos hε)] with n hn
  have hyn : ‖centralVectorDefect J ξ (y n).val‖ < ε/2 := by
    simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hn
  have hsmall : C * ‖x-y‖ < ε/2 := by
    have hm := (lt_div_iff₀ hden).mp hnxy
    nlinarith [norm_nonneg (x-y)]
  have he : centralVectorDefect J ξ (x n).val =
      centralVectorDefect J ξ ((x-y) n).val + centralVectorDefect J ξ (y n).val := by
    change centralVectorDefect J ξ (x n).val =
      centralVectorDefect J ξ ((x n).val-(y n).val) + centralVectorDefect J ξ (y n).val
    rw [map_sub,sub_add_cancel]
  have hb : ‖centralVectorDefect J ξ ((x-y) n).val‖ ≤ C * ‖x-y‖ :=
    (centralVectorDefect_norm_le J hJ ξ _).trans
      (mul_le_mul_of_nonneg_left ((x-y).norm_coe_le_norm n) hC)
  have ht : ‖centralVectorDefect J ξ (x n).val‖ < ε := by
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith)
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using ht

def centralSequenceAlgebra (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) : StarSubalgebra ℂ (BoundedSequence (Algebra M)) where
  carrier := {x | AsymptoticallyCentral J ξ x}
  zero_mem' := by
    change Tendsto (fun _ : ℕ => ‖centralVectorDefect J ξ 0‖) atTop (𝓝 0)
    simpa only [map_zero,norm_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  one_mem' := by
    change Tendsto (fun _ : ℕ => ‖centralVectorDefect J ξ 1‖) atTop (𝓝 0)
    simpa only [centralVectorDefect_one J hJ,norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  add_mem' := AsymptoticallyCentral.add
  mul_mem' := AsymptoticallyCentral.mul hJ hright
  algebraMap_mem' c := by
    change Tendsto (fun _ : ℕ => ‖centralVectorDefect J ξ (algebraMap ℂ (H →L[ℂ] H) c)‖) atTop (𝓝 0)
    rw [Algebra.algebraMap_eq_smul_one,map_smul,centralVectorDefect_one J hJ,smul_zero,norm_zero]
    exact tendsto_const_nhds
  star_mem' := AsymptoticallyCentral.star hJ hξ

theorem centralSequenceAlgebra_isClosed (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) :
    IsClosed (centralSequenceAlgebra J hJ hright ξ hξ : Set (BoundedSequence (Algebra M))) :=
  asymptoticallyCentral_isClosed J hJ ξ

end

end KadisonKastler

end OAI

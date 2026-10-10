import OAI.Analysis.KadisonKastler.StateUnitaryCentralizer

namespace OAI

/-! # Strong convergence from the reference vector and its commutant orbit -/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem commutant_cyclic_of_fixed_conjugation
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ)) :
    DenseRange (algebraVectorMap M.commutant ξ) := by
  have hJ : DenseRange J := J.surjective.denseRange
  have hdense := hJ.comp hcyc J.continuous
  apply Dense.mono _ hdense
  rintro _ ⟨a,rfl⟩
  refine ⟨⟨conjugationOperator J a.val,hright a⟩,?_⟩
  change J (a.val (J ξ))=J (a.val ξ)
  rw [hξ]

theorem commutant_cyclic_of_separating_reference
    (ξ : H) (hsep : Function.Injective (algebraVectorMap M ξ)) :
    DenseRange (algebraVectorMap M.commutant ξ) := by
  let p := vectorSupportProjection M ξ
  have hp : p.val=1 := hsep (by
    change p.val.val ξ=(1 : H →L[ℂ] H) ξ
    exact vectorSupportProjection_apply M ξ)
  have he : (vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection=1 :=
    congrArg (fun a : Algebra M => a.val) hp
  intro η
  have hm := Submodule.starProjection_apply_mem
    (vectorOrbitClosure M.commutant.toStarSubalgebra ξ) η
  rw [he,one_apply_eq_self] at hm
  exact hm

theorem algebra_strong_tendsto_of_reference
    {ι : Type*} {l : Filter ι}
    (ξ : H) (hcyc : DenseRange (algebraVectorMap M.commutant ξ))
    (T : ι → Algebra M) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, ‖T n‖ ≤ C)
    (hξ : Tendsto (fun n => (T n).val ξ) l (𝓝 0)) (η : H) :
    Tendsto (fun n => (T n).val η) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 2*(C+1) := by positivity
  obtain ⟨b,hb⟩ := hcyc.exists_dist_lt η (div_pos hε hden)
  have hnear : ‖η-b.val ξ‖ < ε/(2*(C+1)) := by
    change dist η (b.val ξ) < ε/(2*(C+1)) at hb
    simpa only [dist_eq_norm] using hb
  have hsmall : C*‖η-b.val ξ‖ < ε/2 := by
    have hmul := (lt_div_iff₀ hden).mp hnear
    nlinarith only [hmul,norm_nonneg (η-b.val ξ)]
  have hcomm (n : ι) : (T n).val (b.val ξ)=b.val ((T n).val ξ) :=
    congrArg (fun A : H →L[ℂ] H => A ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp b.property (T n).val (T n).property)
  have hbzero : Tendsto (fun n => (T n).val (b.val ξ)) l (𝓝 0) := by
    have h := b.val.continuous.tendsto (0 : H) |>.comp hξ
    simpa only [hcomm,map_zero,Function.comp_def] using h
  have hbNorm : Tendsto (fun n => ‖(T n).val (b.val ξ)‖) l (𝓝 0) := by
    simpa only [norm_zero] using hbzero.norm
  filter_upwards [hbNorm.eventually (gt_mem_nhds (half_pos hε))] with n hn
  have he : (T n).val η=(T n).val (η-b.val ξ)+(T n).val (b.val ξ) := by
    rw [← map_add,sub_add_cancel]
  have hbn : ‖(T n).val (η-b.val ξ)‖ ≤ C*‖η-b.val ξ‖ :=
    ((T n).val.le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
  have hnη : ‖(T n).val η‖ < ε := by
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith only [hbn,hsmall,hn])
  simpa only [dist_zero_right] using hnη

end

end KadisonKastler

end OAI

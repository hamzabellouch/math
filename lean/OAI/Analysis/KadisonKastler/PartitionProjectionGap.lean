import OAI.Analysis.KadisonKastler.PartitionSignAverage
import OAI.Analysis.KadisonKastler.UnitaryStateDefect

namespace OAI

/-! # One projection retains a finite pinching gap

This is the finite sign-averaging argument in Haagerup, Acta Math. 158
(1987), Lemma 2.16. The reference error is bounded uniformly over all signs.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance projectionOperatorNNRat : Module ℚ≥0 (H →L[ℂ] H) :=
  Module.compHom (H →L[ℂ] H) (algebraMap ℚ≥0 ℂ)

local instance projectionVectorNNRat : Module ℚ≥0 H :=
  Module.compHom H (algebraMap ℚ≥0 ℂ)

def symmetryPositiveProjection (u : Algebra M) (hu : star u=u) (h2 : u*u=1) :
    AlgebraProjection M :=
  ⟨(1/2:ℝ) • (1+u), by
    constructor
    · change ((1/2:ℝ) • (1+u))*((1/2:ℝ) • (1+u))=(1/2:ℝ) • (1+u)
      simp only [smul_mul_assoc,mul_smul_comm,mul_add,add_mul,one_mul,mul_one,h2]
      module
    · change star ((1/2:ℝ) • (1+u))=(1/2:ℝ) • (1+u)
      rw [star_smul,star_trivial,star_add,star_one,hu]⟩

theorem symmetryPositiveProjection_defect (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (u : Algebra M) (hu : star u=u) (h2 : u*u=1) (x : H) :
    centralVectorDefect J x (symmetryPositiveProjection u hu h2).val.val=
      (1/2:ℝ) • centralVectorDefect J x u.val := by
  change centralVectorDefect J x ((1/2:ℝ) • (1+u.val))=_
  rw [(centralVectorDefect J x).map_smul_of_tower,map_add,centralVectorDefect_one J hJ,
    zero_add]

omit [DecidableEq ι] in
theorem partition_sign_defect_on_pinching (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → AlgebraProjection M) (R : H →L[ℂ] H)
    (hc : ∀ i x, (P i).val.val (R x)=conjugationOperator J (P i).val.val (R x))
    (ε : ι → Bool) (x : H) :
    centralVectorDefect J (R x) (partitionSignOperator P ε).val=0 := by
  rw [partitionSignOperator_val]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [(centralVectorDefect J (R x)).map_smul_of_tower,centralVectorDefect_apply]
  have hs : star (P i).val.val=(P i).val.val :=
    congrArg Subtype.val (P i).property.isSelfAdjoint.star_eq
  rw [hs,hc,sub_self,smul_zero]

theorem exists_partition_projection_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (P : ι → AlgebraProjection M)
    (hP : Pairwise (fun i j => (P i).val*(P j).val=0))
    (hs : (∑ i, (P i).val)=1) (R : H →L[ℂ] H)
    (hR : (∑ i, modularQuadratic J (P i).val)=R)
    (hc : ∀ i x, (P i).val.val (R x)=conjugationOperator J (P i).val.val (R x))
    (ξ η : H) :
    ∃ p : AlgebraProjection M,
      ‖centralVectorDefect J ξ p.val.val‖^2 ≤ ‖(1-R) ξ‖^2 ∧
      (1/4:ℝ)*‖(1-R) η‖^2 ≤ ‖centralVectorDefect J η p.val.val‖^2 := by
  let ev : (H →L[ℂ] H) →ₗ[ℚ≥0] H :=
    { toFun := fun T => T η
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hav : (𝔼 ε : ι → Bool, modularQuadratic J (partitionSignOperator P ε) η)=R η := by
    change (𝔼 ε : ι → Bool, ev (modularQuadratic J (partitionSignOperator P ε)))=ev R
    rw [← map_expect ev]
    exact congrArg ev ((expect_partitionSignOperator_quadratic J P).trans hR)
  have he : (𝔼 ε : ι → Bool, (η-modularQuadratic J (partitionSignOperator P ε) η))=η-R η := by
    rw [Finset.expect_sub_distrib,Fintype.expect_const,hav]
  have hn : ‖η-R η‖ ≤ 𝔼 ε : ι → Bool, ‖η-modularQuadratic J (partitionSignOperator P ε) η‖ := by
    rw [← he]
    apply Finset.le_expect_of_subadditive norm_zero norm_add_le
    intro q x
    rw [← NNRat.cast_smul_eq_nnqsmul ℝ,norm_smul,Real.norm_of_nonneg (by positivity)]
    simpa only [smul_eq_mul] using
      NNRat.cast_smul_eq_nnqsmul ℝ ((q : ℚ≥0)⁻¹) ‖x‖
  obtain ⟨ε,_,hε⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hn
  let u := partitionSignOperator P ε
  have hu : star u=u := partitionSignOperator_star P ε
  have h2 : u*u=1 := partitionSignOperator_sq P hP hs ε
  have hum : u∈unitary (Algebra M) := partitionSignOperator_unitary P hP hs ε
  let p := symmetryPositiveProjection u hu h2
  have hdu (x : H) : ‖centralVectorDefect J x u.val‖=‖x-modularQuadratic J u x‖ := by
    have hu' : star (⟨u,hum⟩ : unitary (Algebra M))=⟨u,hum⟩ := Subtype.ext hu
    rw [centralVectorDefect_unitary_norm_eq J hJ x ⟨u,hum⟩,hu',modularUnitary_coe,norm_sub_rev]
  have hsmall : ‖centralVectorDefect J ξ u.val‖ ≤ 2*‖(1-R) ξ‖ := by
    have hz := partition_sign_defect_on_pinching J P R hc ε ξ
    have hd : centralVectorDefect J (ξ-R ξ) u.val=centralVectorDefect J ξ u.val := by
      simp only [centralVectorDefect_apply,map_sub] at hz ⊢
      rw [sub_sub_sub_comm,hz,sub_zero]
    have hh := centralVectorDefect_norm_le J hJ (ξ-R ξ) u.val
    rw [hd] at hh
    exact hh.trans (by
      change 2*‖ξ-R ξ‖*‖u‖ ≤ 2*‖ξ-R ξ‖
      exact mul_le_of_le_one_right (by positivity) (norm_unitary_le_one ⟨u,hum⟩))
  have hpdef (x : H) : ‖centralVectorDefect J x p.val.val‖=
      (1/2:ℝ)*‖centralVectorDefect J x u.val‖ := by
    rw [symmetryPositiveProjection_defect J hJ u hu h2,norm_smul]
    norm_num
  refine ⟨p,?_,?_⟩
  · rw [hpdef]
    have hn0 := norm_nonneg (centralVectorDefect J ξ u.val)
    have hn1 := norm_nonneg ((1-R) ξ)
    nlinarith only [hsmall,hn0,hn1]
  · rw [hpdef,hdu]
    change (1/4:ℝ)*‖η-R η‖^2 ≤ ((1/2:ℝ)*‖η-modularQuadratic J u η‖)^2
    have hn0 := norm_nonneg (η-R η)
    have hn1 := norm_nonneg (η-modularQuadratic J u η)
    nlinarith only [hε,hn0,hn1]

end

end KadisonKastler

end OAI

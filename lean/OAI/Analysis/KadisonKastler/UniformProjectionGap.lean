import OAI.Analysis.KadisonKastler.PartitionProjectionGap

namespace OAI

/-! # Uniform projection witnesses from modular coisometries -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance uniformGapRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem exists_projection_gap_of_finite_pinching
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (T : Set (AlgebraProjection M)) (hT : T.Finite)
    (horth : T.Pairwise (fun p q => p.val*q.val=0)) (ξ η : H) :
    ∃ p : AlgebraProjection M,
      ‖centralVectorDefect J ξ p.val.val‖^2 ≤ ‖(1-projectionFamilyPinching J T) ξ‖^2 ∧
      (1/4:ℝ)*‖(1-projectionFamilyPinching J T) η‖^2 ≤
        ‖centralVectorDefect J η p.val.val‖^2 := by
  classical
  let F := hT.toFinset
  have he : (F : Set (AlgebraProjection M))=T := hT.coe_toFinset
  have hF : (F : Set (AlgebraProjection M)).Pairwise (fun p q => p.val*q.val=0) := he ▸ horth
  obtain ⟨hs,hr⟩ := finitePartitionProjection_sum J hJ hright F hF
  have hc : ∀ i x, (finitePartitionProjection F i).val.val (projectionFamilyPinching J T x)=
      conjugationOperator J (finitePartitionProjection F i).val.val (projectionFamilyPinching J T x) := by
    intro i x
    have hx : projectionFamilyPinching J T x ∈ projectionFamilyCommutationSpace J T :=
      Submodule.starProjection_apply_mem _ _
    cases i with
    | none =>
      change (projectionFamilyRemainder (F : Set (AlgebraProjection M))).val.val
        (projectionFamilyPinching J T x)=conjugationOperator J
          (projectionFamilyRemainder (F : Set (AlgebraProjection M))).val.val
          (projectionFamilyPinching J T x)
      rw [he]
      exact projectionFamily_remainder_central J hJ hright T hx
    | some p =>
      exact (mem_projectionFamilyCommutationSpace J T _).mp hx p.val (he ▸ p.property)
  rw [he] at hr
  exact exists_partition_projection_gap J hJ (finitePartitionProjection F)
    (finitePartitionProjection_orthogonal F hF) hs _ hr hc ξ η

variable [TopologicalSpace.SeparableSpace H]

theorem exists_uniform_projection_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (huξ : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hIII : TypeIIIFactor M) (hremote : UniversalModularCoisometries M J)
    (η : H) (hη : J η=η) (huη : ‖η‖=1) (horth : inner ℂ ξ η=0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : AlgebraProjection M,
      ‖centralVectorDefect J ξ p.val.val‖^2 < δ ∧
      (1/8388608:ℝ) < ‖centralVectorDefect J η p.val.val‖^2 := by
  obtain ⟨T,hT,_,hTorth,hgap,hsmall⟩ := exists_finite_uniform_pinching_gap J hJ hright
    hleft ξ hξ huξ hsep hpos hIII hremote η hη huη horth δ hδ
  obtain ⟨p,hpξ,hpη⟩ := exists_projection_gap_of_finite_pinching J hJ hright T hT hTorth ξ η
  have hnorm := projection_apply_norm_le (projectionFamilyPinching_isProjection J T).one_sub η
  rw [huη] at hnorm
  have hsquare : ‖(1-projectionFamilyPinching J T) η‖^2 ≤ 1 := by
    nlinarith [norm_nonneg ((1-projectionFamilyPinching J T) η)]
  refine ⟨p,hpξ.trans_lt (hsmall.trans_le ?_),?_⟩
  · exact mul_le_of_le_one_right hδ.le hsquare
  · linarith only [hgap,hpη]

end

end KadisonKastler

end OAI

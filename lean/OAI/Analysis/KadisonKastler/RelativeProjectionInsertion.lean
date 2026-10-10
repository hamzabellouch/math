import OAI.Analysis.KadisonKastler.RelativeMatrixPreparation
import OAI.Analysis.KadisonKastler.RelativeBicentralizerGap

namespace OAI

/-! # Inserting a bicentralizer projection cut into a larger matrix stage

The fixed residual gap survives exact containment of the chosen projection.
The reference displacement can be made arbitrarily small.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

local instance relativeInsertionRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem TypeIIIFactor.exists_relative_projection_insertion
    (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (hhom : FaithfulVectorStateHomogeneity E.units.relativeVonNeumann)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (ω : H) (hω : ω ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖ω‖=1)
    (hsep : Function.Injective (algebraVectorMap M ω))
    (hωE : ω ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J)
    (hscalar : ∀ b : Algebra E.units.relativeVonNeumann, stateBicentralizerMember ω b →
      ∃ z : ℂ, b=z • 1)
    (η : H) (hη : η≠0) (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J)
    (horth : inner ℂ ω η=0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (F : FiniteMatrixStage M) (p : AlgebraProjection M) (ζ : H),
      E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      p.val.val ∈ F.units.concreteAlgebra ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) J ∧
      ‖ζ-ω‖ ≤ δ ∧
      (1/128:ℝ)*‖η‖^2 ≤ ‖p.val.val η-conjugationOperator J p.val.val η‖^2 := by
  let : Nonempty (Fin E.size) := ⟨⟨0,E.positive⟩⟩
  let a : ℝ := min (1/2) (δ^2/16)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  obtain ⟨p,hpr,hpg⟩ := exists_relative_projection_residual_gap E.units J hJ hright hleft
    ξ hξ hcyc hpos ω hω hunit hsep hωE hscalar η hη hηE horth (a^2/2) (by positivity)
  have hsmall : ‖p.val.val ω-conjugationOperator J p.val.val ω‖ < a := by
    change ‖p.val.val ω-conjugationOperator J p.val.val ω‖^2 ≤ a^2/2 at hpr
    nlinarith [norm_nonneg (p.val.val ω-conjugationOperator J p.val.val ω)]
  have hpositive : 0 < (1/128:ℝ)*‖η‖^2 := by
    exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hη))
  have hzero : conjugationOperator J (0 : H →L[ℂ] H)=0 := by
    ext x
    exact map_zero J
  have hp0 : p.val≠0 := by
    intro hz
    have he : p.val.val=0 := congrArg Subtype.val hz
    rw [he,hzero,sub_self,zero_apply,norm_zero] at hpg
    norm_num at hpg
    linarith
  have hp1 : p.val≠1 := by
    intro hz
    have he : p.val.val=1 := congrArg Subtype.val hz
    rw [he,conjugationOperator_one J hJ,sub_self,zero_apply,norm_zero] at hpg
    norm_num at hpg
    linarith
  have hsmall1 : ‖p.val.val ω-conjugationOperator J p.val.val ω‖ < 1 :=
    hsmall.trans_le ((min_le_left _ _).trans (by norm_num))
  have hsmallδ : ‖p.val.val ω-conjugationOperator J p.val.val ω‖ < δ^2/8 := by
    have hh : a ≤ δ^2/16 := min_le_right _ _
    have hd : 0 < δ^2 := sq_pos_of_pos hδ
    linarith
  obtain ⟨F,ζ,hEF,hpF,_,_,_,hζF,hclose⟩ :=
    hM.exists_relative_matrix_stage_near_projection E hhom J hJ hright hleft ξ hξ hcyc
      hpos ω hω hunit hsep hωE p hp0 hp1 hsmall1 δ hδ hsmallδ
  let f := StarSubalgebra.inclusion E.units.relativeVonNeumann_le
  let pM : AlgebraProjection M := ⟨f p.val,p.property.map f⟩
  exact ⟨F,pM,ζ,hEF,hpF,hζF,hclose.le,hpg⟩

end

end KadisonKastler

end OAI

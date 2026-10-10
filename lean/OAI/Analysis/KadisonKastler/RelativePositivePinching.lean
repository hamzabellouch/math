import OAI.Analysis.KadisonKastler.RelativeUnitaryStateDefect
import OAI.Analysis.KadisonKastler.NormalizedPositivePinching

namespace OAI

/-! # Positive pinching that preserves the initial matrix centralizer -/

namespace KadisonKastler

open Generator Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance relativePinchRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_relative_positive_projection_central_unit_vector
    (E : FiniteMatrixStage M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (η : H) (hη : η ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖η‖=1)
    (hsep : Function.Injective (algebraVectorMap M η))
    (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J)
    (p : AlgebraProjection E.units.relativeVonNeumann)
    (hgap : ‖p.val.val η-conjugationOperator J p.val.val η‖ < 1) :
    ∃ ζ : H, ‖ζ‖=1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J ∧
      p.val.val ζ=conjugationOperator J p.val.val ζ ∧
      ‖ζ-η‖ ≤ 2*‖p.val.val η-conjugationOperator J p.val.val η‖ := by
  let f := StarSubalgebra.inclusion E.units.relativeVonNeumann_le
  let pM : AlgebraProjection M := ⟨f p.val,p.property.map f⟩
  let y := positiveVectorPinch J pM η
  have he := positiveVectorPinch_norm_sub J hJ hright pM η
  have hy : y ≠ 0 := by
    intro hz
    change ‖y-η‖ = _ at he
    rw [hz,zero_sub,norm_neg,hunit] at he
    change 1=‖p.val.val η-conjugationOperator J p.val.val η‖ at he
    linarith
  have hycone := positiveVectorPinch_mem_cone J hJ hright ξ pM hη
  have hysep := positiveVectorPinch_separating J hJ hright ξ hξ hpos pM hη hsep
  have hyE : y ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J := by
    change positiveVectorPinch J pM η ∈ _
    rw [positiveVectorPinch_eq J hJ]
    exact (centralVectorSpace (matrixUnitConcreteAlgebra E.units) J).add_mem
      (relative_modularQuadratic_mem_central E.units J hJ hright p.val hηE)
      (relative_modularQuadratic_mem_central E.units J hJ hright (1-p.val) hηE)
  have hscalar : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  have hζcone : normalize y ∈ modularPositiveCone (M := M) J ξ :=
    (modularPositiveCone J ξ).smul_mem hscalar hycone
  have hζsep : Function.Injective (algebraVectorMap M (normalize y)) := by
    intro a b hab
    apply hysep
    change a.val y=b.val y
    change a.val (‖y‖⁻¹ • y)=b.val (‖y‖⁻¹ • y) at hab
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
    exact smul_right_injective H hscalar.ne' hab
  refine ⟨normalize y,norm_normalize hy,hζcone,hζsep,?_,?_,?_⟩
  · exact (centralVectorSpace (matrixUnitConcreteAlgebra E.units) J).smul_of_tower_mem
      (‖y‖⁻¹) hyE
  · change p.val.val (‖y‖⁻¹ • y)=conjugationOperator J p.val.val (‖y‖⁻¹ • y)
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower]
    exact congrArg (fun z : H => ‖y‖⁻¹ • z)
      (positiveVectorPinch_centralizes_projection J hJ hright pM η)
  · exact (norm_normalize_sub_le_twice hunit hy).trans_eq (congrArg (2*·) he)

end

end KadisonKastler

end OAI

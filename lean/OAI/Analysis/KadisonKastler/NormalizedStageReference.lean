import OAI.Analysis.KadisonKastler.NormalizedMatrixAveraging
import OAI.Analysis.KadisonKastler.MatrixCentralRefinement

namespace OAI

/-! # Normalizing the faithful projected reference vector -/

namespace KadisonKastler

open Generator Generator.Tracial NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance normalizedStageRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_normalized_matrix_reference
    (E : FiniteMatrixStage M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (hunit : ‖ξ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ)) :
    ∃ (ω : H) (n : ℝ), 0 < n ∧ n ≤ 1 ∧ n • ω=matrixStageCentralProjection E J ξ ∧
      ‖ω‖=1 ∧ ω ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ω) ∧
      ω ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J := by
  let : Nonempty (Fin E.size) := ⟨⟨0,E.positive⟩⟩
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E.units) J
  let y := K.starProjection ξ
  have hycone : y ∈ modularPositiveCone (M := M) J ξ :=
    matrixCentralProjection_preserves_positiveCone E.units J hJ hright ξ ⟨0,E.positive⟩
      (reference_mem_modularPositiveCone J hJ ξ)
  have hysep := matrixCentralProjection_separating J hJ hright ξ hξ hpos E.units
    (reference_mem_modularPositiveCone J hJ ξ) hsep
  have hy : y≠0 := by
    intro hz
    have he : (1 : Algebra M)=0 := hysep (by
      change (1 : Algebra M).val y=(0 : Algebra M).val y
      rw [hz]
      simp)
    have hv : ξ=0 := by
      have hv := congrArg (fun a : Algebra M => a.val ξ) he
      simpa using hv
    have hn := norm_eq_zero.mpr hv
    linarith
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hscalar : 0 < ‖y‖⁻¹ := inv_pos.mpr hn
  have hωsep : Function.Injective (algebraVectorMap M (normalize y)) := by
    intro a b hab
    apply hysep
    change a.val y=b.val y
    change a.val (‖y‖⁻¹ • y)=b.val (‖y‖⁻¹ • y) at hab
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
    exact smul_right_injective H hscalar.ne' hab
  refine ⟨normalize y,‖y‖,hn,?_,norm_smul_normalize y,norm_normalize hy,
    (modularPositiveCone J ξ).smul_mem hscalar hycone,hωsep,?_⟩
  · exact (K.norm_starProjection_apply_le ξ).trans_eq hunit
  · exact K.smul_of_tower_mem (‖y‖⁻¹) (Submodule.starProjection_apply_mem K ξ)

end

end KadisonKastler

end OAI

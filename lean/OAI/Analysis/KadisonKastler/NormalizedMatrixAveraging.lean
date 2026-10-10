import OAI.Analysis.KadisonKastler.RelativeCentralStandardSpace
import OAI.Analysis.KadisonKastler.NormalizedPositivePinching

namespace OAI

/-! # Faithful central unit vectors from finite matrix averaging

The explicit central-vector projection of a faithful positive unit vector
is nonzero. Normalizing it retains positivity, faithfulness and cyclicity,
with at most twice the displacement of the orthogonal projection.
-/

namespace KadisonKastler

open Generator NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance normalizedMatrixRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem exists_positive_matrix_central_unit_vector
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hunit : ‖η‖ = 1) (hsep : Function.Injective (algebraVectorMap M η)) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧ ζ ∈ modularPositiveCone (M := M) J ξ ∧
      Function.Injective (algebraVectorMap M ζ) ∧ DenseRange (algebraVectorMap M ζ) ∧
      ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ∧
      ‖ζ-η‖ ≤ 2 * ‖(centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η-η‖ := by
  classical
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E) J
  let y := K.starProjection η
  let o : ι := Classical.choice inferInstance
  have hycone : y ∈ modularPositiveCone (M := M) J ξ :=
    matrixCentralProjection_preserves_positiveCone E J hJ hright ξ o hη
  have hysep : Function.Injective (algebraVectorMap M y) :=
    matrixCentralProjection_separating J hJ hright ξ hξ hpos E hη hsep
  have hy : y ≠ 0 := by
    intro hz
    have he : (1 : Algebra M) = 0 := hysep (by
      change (1 : Algebra M).val y = (0 : Algebra M).val y
      rw [hz]
      simp)
    have hv : η = 0 := by
      have hv := congrArg (fun a : Algebra M => a.val η) he
      simpa using hv
    have hn := norm_eq_zero.mpr hv
    linarith
  have hscalar : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  have hζcone : normalize y ∈ modularPositiveCone (M := M) J ξ :=
    (modularPositiveCone J ξ).smul_mem hscalar hycone
  have hζsep : Function.Injective (algebraVectorMap M (normalize y)) := by
    intro a b hab
    apply hysep
    change a.val y = b.val y
    change a.val (‖y‖⁻¹ • y) = b.val (‖y‖⁻¹ • y) at hab
    rw [ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower] at hab
    exact smul_right_injective H hscalar.ne' hab
  refine ⟨normalize y,norm_normalize hy,hζcone,hζsep,?_,?_,?_⟩
  · exact cyclic_of_separating_of_conjugation_fixed J hJ hleft
      (modularPositiveCone_fixed J hright ξ hξ hζcone) hζsep
  · exact K.smul_mem (‖y‖⁻¹ : ℝ) (Submodule.starProjection_apply_mem K η)
  · exact norm_normalize_sub_le_twice hunit hy

end

end KadisonKastler

end OAI

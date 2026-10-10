import OAI.Analysis.KadisonKastler.MatrixProjectionCut

namespace OAI

/-! # The part of a matrix-central vector orthogonal to the reference line -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixCentralResidual (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) : H :=
  matrixStageCentralProjection E J η -
    (Submodule.span ℂ {matrixStageCentralProjection E J ξ}).starProjection
      (matrixStageCentralProjection E J η)

theorem matrixCentralResidual_coefficient
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    ∃ c : ℂ, matrixCentralResidual E J ξ η =
      matrixStageCentralProjection E J η - c • matrixStageCentralProjection E J ξ := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.span ℂ {matrixStageCentralProjection E J ξ}).starProjection_apply_mem
      (matrixStageCentralProjection E J η))
  exact ⟨c,by rw [matrixCentralResidual,← hc]⟩

theorem matrixCentralResidual_mem
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    matrixCentralResidual E J ξ η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J := by
  obtain ⟨c,hc⟩ := matrixCentralResidual_coefficient E J ξ η
  rw [hc]
  exact Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _)
    (Submodule.smul_mem _ c (Submodule.starProjection_apply_mem _ _))

theorem matrixCentralResidual_orthogonal
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    inner ℂ (matrixCentralResidual E J ξ η) (matrixStageCentralProjection E J ξ) = 0 :=
  (Submodule.span ℂ {matrixStageCentralProjection E J ξ}).starProjection_inner_eq_zero
    _ _ (Submodule.mem_span_singleton_self _)

theorem matrixCentralResidual_norm_le
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (c : ℂ) :
    ‖matrixCentralResidual E J ξ η‖ ≤
      ‖matrixStageCentralProjection E J η - c • matrixStageCentralProjection E J ξ‖ :=
  centralProjection_displacement_le_of_central_vector
    (Submodule.span ℂ {matrixStageCentralProjection E J ξ}) _ _
    (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

theorem matrixCentralResidual_refinement_le
    (E F : FiniteMatrixStage M) (hEF : E.units.concreteAlgebra ≤ F.units.concreteAlgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    ‖matrixCentralResidual F J ξ η‖ ≤
      ‖matrixStageCentralProjection F J (matrixCentralResidual E J ξ η)‖ := by
  obtain ⟨c,hc⟩ := matrixCentralResidual_coefficient E J ξ η
  have hcomp : matrixStageCentralProjection F J ∘L matrixStageCentralProjection E J =
      matrixStageCentralProjection F J :=
    Submodule.starProjection_comp_starProjection_of_le (centralVectorSpace_antitone hEF J)
  have he (x : H) : matrixStageCentralProjection F J (matrixStageCentralProjection E J x) =
      matrixStageCentralProjection F J x :=
    congrArg (fun T : H →L[ℂ] H => T x) hcomp
  rw [hc,map_sub,map_smul,he,he]
  exact matrixCentralResidual_norm_le F J ξ η c

end

end KadisonKastler

end OAI

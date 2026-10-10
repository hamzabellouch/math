import OAI.Analysis.FiniteFactor.CrossedProduct.NormalRiesz
import OAI.Analysis.FiniteFactor.Model
import Mathlib.Analysis.CStarAlgebra.Basic

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

/-- The reconstructed operator belongs to the original algebra, by its
verified double-commutant definition. -/
theorem sourceNormalRieszOperator_mem (θ : SourceCoordinate → ℝ)
    (F : StrongDual ℂ (SourceNormalPredualSpace θ)) :
    sourceNormalRieszOperator θ F ∈ sourceAlgebra θ := by
  rw [← (sourceAlgebra θ).commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  change inner ℂ ξ (b (sourceNormalRieszOperator θ F η)) =
    inner ℂ ξ (sourceNormalRieszOperator θ F (b η))
  have hv : sourceVectorInSpace θ ξ (b η) = sourceVectorInSpace θ (star b ξ) η := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro A
    change inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (b η)) =
      inner ℂ (star b ξ) ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) η)
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      inner ℂ ξ (T η)) ((VonNeumannAlgebra.mem_commutant_iff.mp hb) A A.property)
  calc
    _ = inner ℂ (star b ξ) (sourceNormalRieszOperator θ F η) :=
      (ContinuousLinearMap.adjoint_inner_left b (sourceNormalRieszOperator θ F η) ξ).symm
    _ = F (sourceVectorInSpace θ (star b ξ) η) := sourceNormalRieszOperator_inner θ F _ η
    _ = F (sourceVectorInSpace θ ξ (b η)) := congrArg F hv.symm
    _ = _ := (sourceNormalRieszOperator_inner θ F ξ (b η)).symm

/-- Equality on actual vector functionals determines a functional on their
closed span. -/
theorem sourceNormalFunctionals_ext (θ : SourceCoordinate → ℝ)
    (F G : StrongDual ℂ (SourceNormalPredualSpace θ))
    (h : ∀ ξ η, F (sourceVectorInSpace θ ξ η) = G (sourceVectorInSpace θ ξ η)) : F = G := by
  let S : Submodule ℂ (StrongDual ℂ (SourceAlgebraSpace θ)) :=
    Submodule.span ℂ (Set.range (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
      sourceVectorFunctional θ z.1 z.2))
  have hs : ∀ φ ∈ S, ∀ hφ : φ ∈ sourceNormalFunctionalSpace θ, F ⟨φ,hφ⟩ = G ⟨φ,hφ⟩ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨⟨ξ,η⟩,rfl⟩ := hφ
      intro _
      exact h ξ η
    | zero => intro _; exact (map_zero F).trans (map_zero G).symm
    | add φ ψ hφ hψ ihφ ihψ =>
      intro hsum
      have hφ' := Submodule.le_topologicalClosure S hφ
      have hψ' := Submodule.le_topologicalClosure S hψ
      change F (⟨φ,hφ'⟩+⟨ψ,hψ'⟩) = G (⟨φ,hφ'⟩+⟨ψ,hψ'⟩)
      exact (F.map_add ⟨φ,hφ'⟩ ⟨ψ,hψ'⟩).trans
        ((congrArg₂ (· + ·) (ihφ hφ') (ihψ hψ')).trans (G.map_add ⟨φ,hφ'⟩ ⟨ψ,hψ'⟩).symm)
    | smul c φ hφ ihφ =>
      intro hsmul
      have hφ' := Submodule.le_topologicalClosure S hφ
      change F (c • ⟨φ,hφ'⟩) = G (c • ⟨φ,hφ'⟩)
      exact (F.map_smul c ⟨φ,hφ'⟩).trans
        ((congrArg (fun z : ℂ => c • z) (ihφ hφ')).trans (G.map_smul c ⟨φ,hφ'⟩).symm)
  let j : S → SourceNormalPredualSpace θ := fun φ => ⟨φ,Submodule.le_topologicalClosure S φ.property⟩
  have hd : DenseRange j := (denseRange_inclusion_iff (Submodule.le_topologicalClosure S)).mpr
    (by intro φ hφ; exact hφ)
  apply ContinuousLinearMap.ext
  intro φ
  have hsub : Set.range j ⊆ {ψ | F ψ = G ψ} := by
    rintro ψ ⟨χ,rfl⟩
    exact hs χ χ.property _
  exact (closure_minimal hsub (isClosed_eq F.continuous G.continuous)) (hd φ)

/-- Every continuous functional on the constructed separable Banach space
is evaluation by an element of the original source algebra. -/
theorem sourceNormalEvaluation_surjective (θ : SourceCoordinate → ℝ) :
    Function.Surjective (sourceNormalEvaluation θ) := by
  intro F
  refine ⟨⟨sourceNormalRieszOperator θ F,sourceNormalRieszOperator_mem θ F⟩,?_⟩
  apply sourceNormalFunctionals_ext
  intro ξ η
  exact sourceNormalRieszOperator_inner θ F ξ η

theorem sourceNormalEvaluation_norm (θ : SourceCoordinate → ℝ) (A : SourceAlgebraSpace θ) :
    ‖sourceNormalEvaluation θ A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro φ
    change ‖(φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)) A‖ ≤ _
    exact ((φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)).le_opNorm A).trans_eq (mul_comm _ _)
  · have he : sourceNormalRieszOperator θ (sourceNormalEvaluation θ A) =
        (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) := by
      apply ContinuousLinearMap.ext
      intro η
      apply ext_inner_left ℂ
      intro ξ
      exact sourceNormalRieszOperator_inner θ (sourceNormalEvaluation θ A) ξ η
    change ‖(A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)‖ ≤ _
    rw [← he]
    exact sourceNormalRieszOperator_norm θ (sourceNormalEvaluation θ A)

def sourceNormalEvaluationIsometry (θ : SourceCoordinate → ℝ) :
    SourceAlgebraSpace θ →ₗᵢ[ℂ] StrongDual ℂ (SourceNormalPredualSpace θ) where
  toFun := sourceNormalEvaluation θ
  map_add' A B := by apply ContinuousLinearMap.ext; intro φ; exact map_add (φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)) A B
  map_smul' c A := by apply ContinuousLinearMap.ext; intro φ; exact map_smul (φ.1 : StrongDual ℂ (SourceAlgebraSpace θ)) c A
  norm_map' := sourceNormalEvaluation_norm θ

/-- The full dual identification, with the exact conjugate-linear convention
required by Target.HasSeparablePredual. -/
def sourcePredualIdentification (θ : SourceCoordinate → ℝ) :
    StrongDual ℂ (SourceNormalPredualSpace θ) ≃ₗᵢ⋆[ℂ] SourceAlgebraSpace θ :=
  (LinearIsometryEquiv.ofSurjective (sourceNormalEvaluationIsometry θ)
    (sourceNormalEvaluation_surjective θ)).symm.trans (starₗᵢ ℂ)

theorem sourceAlgebra_hasSeparablePredual (θ : SourceCoordinate → ℝ) :
    HasSeparablePredual (sourceAlgebra θ) := by
  refine ⟨SourceNormalPredualSpace θ,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  exact ⟨sourcePredualIdentification θ⟩

end
end FiniteFactor

end OAI

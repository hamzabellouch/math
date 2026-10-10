import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! # Regarding finite stages as subalgebras of their own closure -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def matrixStagesInClosure (A : ℕ → FiniteMatrixStage M) (n : ℕ) :
    FiniteMatrixStage (FiniteMatrixStage.generatedVonNeumann A) where
  size := (A n).size
  positive := (A n).positive
  units := {
    entry := fun i j => ⟨((A n).units.entry i j).val,
      FiniteMatrixStage.stage_le_generated A n
        (((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j))⟩
    star_entry := by
      intro i j
      apply Subtype.ext
      change star ((A n).units.entry i j).val = ((A n).units.entry j i).val
      exact congrArg (fun a : M.toStarSubalgebra => a.val) ((A n).units.star_entry i j)
    mul_entry := by
      intro i j k l
      apply Subtype.ext
      by_cases h : j = k
      · simp only [ite_eq_left h]
        change ((A n).units.entry i j).val * ((A n).units.entry k l).val =
          ((A n).units.entry i l).val
        exact congrArg (fun a : M.toStarSubalgebra => a.val)
          (((A n).units.mul_entry i j k l).trans (ite_eq_left h))
      · simp only [ite_eq_right h]
        change ((A n).units.entry i j).val * ((A n).units.entry k l).val = 0
        exact congrArg (fun a : M.toStarSubalgebra => a.val)
          (((A n).units.mul_entry i j k l).trans (ite_eq_right h))
    total := by
      apply Subtype.ext
      change (FiniteMatrixStage.generatedVonNeumann A).toStarSubalgebra.subtype
        (∑ i, (⟨((A n).units.entry i i).val, _⟩ :
          (FiniteMatrixStage.generatedVonNeumann A).toStarSubalgebra)) = 1
      rw [map_sum]
      have h := congrArg M.toStarSubalgebra.subtype (A n).units.total
      simp only [map_sum, map_one] at h
      change (∑ i, ((A n).units.entry i i).val) = 1 at h ⊢
      exact h }

theorem matrixStagesInClosure_algebra (A : ℕ → FiniteMatrixStage M) (n : ℕ) :
    (matrixStagesInClosure A n).units.concreteAlgebra = (A n).units.concreteAlgebra := by
  have h : (matrixStagesInClosure A n).units.concreteHom = (A n).units.concreteHom := by
    apply DFunLike.ext
    intro a
    change (FiniteMatrixStage.generatedVonNeumann A).toStarSubalgebra.subtype
      (∑ i, ∑ j, a i j • (matrixStagesInClosure A n).units.entry i j) =
      M.toStarSubalgebra.subtype (∑ i, ∑ j, a i j • (A n).units.entry i j)
    simp only [map_sum, map_smul]
    rfl
  exact congrArg StarAlgHom.range h

theorem matrixStagesInClosure_generated (A : ℕ → FiniteMatrixStage M) :
    FiniteMatrixStage.generatedVonNeumann (matrixStagesInClosure A) =
      FiniteMatrixStage.generatedVonNeumann A := by
  apply SetLike.coe_injective
  change (FiniteMatrixStage.generated (matrixStagesInClosure A) : Set (H →L[ℂ] H)) =
    (FiniteMatrixStage.generated A : Set (H →L[ℂ] H))
  simp only [FiniteMatrixStage.generated, matrixStagesInClosure_algebra]

end

end KadisonKastler

end OAI

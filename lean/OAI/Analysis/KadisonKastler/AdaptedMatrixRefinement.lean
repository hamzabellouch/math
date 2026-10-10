import OAI.Analysis.KadisonKastler.OrthonormalMatrixUnits
import OAI.Analysis.KadisonKastler.SignedMatrixRefinement

namespace OAI

/-! # Refining matrix units while retaining their finite signed group -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (E : Generator.MatrixUnitSystem ι (H →L[ℂ] H)) (o : ι)
  (b : OrthonormalBasis κ ℂ (E.initialHilbertSpace o))

/-- Rank-one units for the adapted basis retain each old matrix entry as
a sum over the new index. -/
theorem adaptedMatrixUnits_retains (i j : ι) :
    ∑ r, (Generator.orthonormalMatrixUnits (E.adaptedBasis o b)).entry (i, r) (j, r) =
      E.entry i j := by
  let B := E.adaptedBasis o b
  change (∑ r, (Generator.orthonormalMatrixUnits B).entry (i, r) (j, r)) = E.entry i j
  have hb (p : ι × κ) :
      (∑ r, (Generator.orthonormalMatrixUnits B).entry (i, r) (j, r)) (B p) =
        E.entry i j (B p) := by
    obtain ⟨k, s⟩ := p
    rw [sum_apply, E.entry_adaptedBasis]
    simp only [Generator.orthonormalMatrixUnits_entry_apply, B.inner_eq_ite, Prod.mk.injEq]
    by_cases h : j = k
    · subst k
      simp [B]
    · simp [h]
  apply ContinuousLinearMap.ext
  intro x
  rw [← B.sum_repr' x]
  simp only [map_sum, map_smul, hb]

/-- This full matrix refinement contains the old finite signed group. -/
theorem adaptedMatrixUnits_group_le :
    matrixSignedGroup E ≤ matrixSignedGroup (Generator.orthonormalMatrixUnits (E.adaptedBasis o b)) :=
  matrixSignedGroup_refinement E _ (adaptedMatrixUnits_retains E o b)

/-- The refined matrix system generates every operator on the finite
Hilbert space and keeps the previous signed group. -/
theorem exists_fullMatrix_refinement [FiniteDimensional ℂ H] (o : ι) :
    ∃ (r : ℕ) (F : Generator.MatrixUnitSystem (ι × Fin r) (H →L[ℂ] H)),
      Function.Surjective F.hom ∧ matrixSignedGroup E ≤ matrixSignedGroup F := by
  let b := stdOrthonormalBasis ℂ (E.initialHilbertSpace o)
  refine ⟨Module.finrank ℂ (E.initialHilbertSpace o),
    Generator.orthonormalMatrixUnits (E.adaptedBasis o b),
    Generator.orthonormalMatrixUnits_surjective _, adaptedMatrixUnits_group_le E o b⟩

end

end KadisonKastler

end OAI

import OAI.Analysis.BoundedHochschild.CountableMatrixSpan
import OAI.Analysis.BoundedHochschild.SignedMatrixUnitaries
import OAI.Analysis.BoundedHochschild.MatrixAmplification

namespace OAI

/-! Finite initial sections of a countable matrix system form full matrix
systems in their actual (possibly proper) corners. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners HochschildMatrixSystems

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {n : ℕ} (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)

def finiteColumnProjection : M := ∑ i, (c i).final

omit [PartialOrder M] [StarOrderedRing M] in
include ho in
lemma finiteColumnProjection_isProjection : IsStarProjection (finiteColumnProjection c) :=
  orthogonal_projection_finset_sum (fun i => (c i).final) (fun i => (c i).final_proj)
    ho Finset.univ

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma finiteColumnProjection_mul_column (j : Fin n) :
    finiteColumnProjection c * (c j : M) = (c j : M) := by
  classical
  simp only [finiteColumnProjection, PartialIso.final, Finset.sum_mul, mul_assoc]
  simp [column_star_mul c hi ho]

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma column_star_mul_finiteColumnProjection (j : Fin n) :
    star (c j : M) * finiteColumnProjection c = star (c j : M) := by
  have h := congrArg star (finiteColumnProjection_mul_column c hi ho j)
  simpa only [star_mul, finiteColumnProjection, star_sum, PartialIso.final, star_star] using h

def finiteColumnMatrixSystem :
    MatrixSystem (Corner (finiteColumnProjection c) (finiteColumnProjection_isProjection c ho)) n where
  entry i j := ⟨(c i : M) * star (c j : M), by
    constructor
    · rw [← mul_assoc, finiteColumnProjection_mul_column c hi ho]
    · rw [mul_assoc, column_star_mul_finiteColumnProjection c hi ho]⟩
  star_entry i j := Subtype.ext (by
    change star ((c i : M) * star (c j : M)) = (c j : M) * star (c i : M)
    simp only [star_mul, star_star])
  entry_mul i j k l := by
    apply Subtype.ext
    change ((c i : M) * star (c j : M)) * ((c k : M) * star (c l : M)) = _
    calc
      _ = (c i : M) * (star (c j : M) * (c k : M)) * star (c l : M) := by
        simp only [mul_assoc]
      _ = _ := by rw [column_star_mul c hi ho]; split_ifs <;> simp
  sum_diagonal := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma finiteColumnMatrixSystem_entry (i j : Fin n) :
    ((finiteColumnMatrixSystem c hi ho).entry i j : M) = (c i : M) * star (c j : M) := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI

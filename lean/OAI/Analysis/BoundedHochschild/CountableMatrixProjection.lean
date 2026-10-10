import OAI.Analysis.BoundedHochschild.CountableMatrixAverage
import OAI.Analysis.BoundedHochschild.MultimodularTransport

namespace OAI

/-! The countable matrix average fixes multimodular cochains and is
therefore an idempotent contraction commuting with the differential. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma matrixSectionAverage_fixes (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1))
    (hf : MultimodularOver (countableMatrixAlgebra c) f) (k : ℕ) :
    matrixSectionAverage c hi ho f k = f :=
  finiteGroupCochainAverage_fixes _ _ f hf (matrixSectionGroup c hi ho k).mem

lemma countableMatrixAverage_fixes (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1))
    (hf : MultimodularOver (countableMatrixAlgebra c) f) : countableMatrixAverage e c hi ho f = f := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho f x)
  have he : (fun k => matrixSectionAverage c hi ho f k x) = fun _ => f x := by
    funext k
    rw [matrixSectionAverage_fixes c hi ho f hf]
  rw [he]
  exact predual_tendsto_const e _ _

variable [CompleteSpace X]

lemma countableMatrixAverage_idempotent (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    countableMatrixAverage e c hi ho (countableMatrixAverage e c hi ho f) =
      countableMatrixAverage e c hi ho f :=
  countableMatrixAverage_fixes e c hi ho _ (countableMatrixAverage_multimodular e c hi ho f)

end BoundedHochschild.KadisonRingrose

end

end OAI

import OAI.Analysis.BoundedHochschild.CountableMatrixAverage
import OAI.Analysis.BoundedHochschild.FiniteGroupBarOperators

namespace OAI

/-! The degree-bounded weak-star limits of the finite matrix-section
bar operators. These use the same groups and ultrafilter as the matrix
cochain projection. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def matrixSectionBarOperator (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (k : ℕ) : Cochain M n :=
  finiteGroupBarOperator (matrixSectionGroup c hi ho k).representation f

lemma matrixSectionBarOperator_norm (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (k : ℕ) : ‖matrixSectionBarOperator c hi ho f k‖ ≤ (n + 1 : ℝ) * ‖f‖ :=
  finiteGroupBarOperator_norm _ f

lemma matrixSectionBarOperator_add (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f g : Cochain M (n + 1)) (k : ℕ) :
    matrixSectionBarOperator c hi ho (f + g) k = matrixSectionBarOperator c hi ho f k + matrixSectionBarOperator c hi ho g k :=
  finiteGroupBarOperator_add _ f g

lemma matrixSectionBarOperator_smul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (z : ℂ) (f : Cochain M (n + 1)) (k : ℕ) :
    matrixSectionBarOperator c hi ho (z • f) k = z • matrixSectionBarOperator c hi ho f k :=
  finiteGroupBarOperator_smul _ z f

private lemma matrix_bar_limit_exists (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    ∃ H : Cochain M n, ‖H‖ ≤ (n + 1 : ℝ) * ‖f‖ ∧ ∀ x,
      PredualTendsto e (fun k => matrixSectionBarOperator c hi ho f k x)
        matrixAverageUltrafilter (H x) :=
  bounded_cochain_ultralimit e matrixAverageUltrafilter (matrixSectionBarOperator c hi ho f)
    ((n + 1 : ℝ) * ‖f‖) (by positivity) (matrixSectionBarOperator_norm c hi ho f)

def countableMatrixBarOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) : Cochain M n :=
  Classical.choose (matrix_bar_limit_exists e c hi ho f)

lemma countableMatrixBarOperator_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    ‖countableMatrixBarOperator e c hi ho f‖ ≤ (n + 1 : ℝ) * ‖f‖ :=
  (Classical.choose_spec (matrix_bar_limit_exists e c hi ho f)).1

lemma countableMatrixBarOperator_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) (x : Fin n → M) :
    PredualTendsto e (fun k => matrixSectionBarOperator c hi ho f k x)
      matrixAverageUltrafilter (countableMatrixBarOperator e c hi ho f x) :=
  (Classical.choose_spec (matrix_bar_limit_exists e c hi ho f)).2 x

lemma countableMatrixBarOperator_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f g : Cochain M (n + 1)) :
    countableMatrixBarOperator e c hi ho (f + g) = countableMatrixBarOperator e c hi ho f + countableMatrixBarOperator e c hi ho g := by
  ext x
  apply predual_tendsto_unique e (countableMatrixBarOperator_tendsto e c hi ho (f + g) x)
  simpa only [matrixSectionBarOperator_add, add_apply] using predual_tendsto_add e
    (countableMatrixBarOperator_tendsto e c hi ho f x) (countableMatrixBarOperator_tendsto e c hi ho g x)

lemma countableMatrixBarOperator_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (z : ℂ) (f : Cochain M (n + 1)) :
    countableMatrixBarOperator e c hi ho (z • f) = z • countableMatrixBarOperator e c hi ho f := by
  ext x
  apply predual_tendsto_unique e (countableMatrixBarOperator_tendsto e c hi ho (z • f) x)
  simpa only [matrixSectionBarOperator_smul, smul_apply] using predual_tendsto_smul e
    (countableMatrixBarOperator_tendsto e c hi ho f x) z

def countableMatrixBarOperatorCLM (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (n : ℕ) :
    Cochain M (n + 1) →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := countableMatrixBarOperator e c hi ho
      map_add' := countableMatrixBarOperator_add e c hi ho
      map_smul' := countableMatrixBarOperator_smul e c hi ho }
    (n + 1) (fun f => by
      change ‖countableMatrixBarOperator e c hi ho f‖ ≤ (n + 1 : ℝ) * ‖f‖
      exact countableMatrixBarOperator_norm e c hi ho f)

end BoundedHochschild.KadisonRingrose

end

end OAI

import OAI.Analysis.BoundedHochschild.MatrixSectionAveraging
import OAI.Analysis.BoundedHochschild.MatrixAverageLimits
import OAI.Analysis.BoundedHochschild.AlgebraicMatrixPrimitives

namespace OAI

/-! A fixed contractive map of the cochain complex into the matrix-unit
multimodular cochains, obtained from the actual finite-group averages.
Its action on cohomology is not asserted here. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def matrixAverageUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

private lemma matrix_average_limit_exists (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) :
    ∃ A : Cochain M n, ‖A‖ ≤ ‖f‖ ∧ ∀ x,
      PredualTendsto e (fun k => matrixSectionAverage c hi ho f k x) matrixAverageUltrafilter (A x) :=
  bounded_cochain_ultralimit e matrixAverageUltrafilter (matrixSectionAverage c hi ho f)
    ‖f‖ (norm_nonneg _) (matrixSectionAverage_norm c hi ho f)

def countableMatrixAverage (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) : Cochain M n :=
  Classical.choose (matrix_average_limit_exists e c hi ho f)

lemma countableMatrixAverage_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) :
    ‖countableMatrixAverage e c hi ho f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (matrix_average_limit_exists e c hi ho f)).1

lemma countableMatrixAverage_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M n) (x : Fin n → M) :
    PredualTendsto e (fun k => matrixSectionAverage c hi ho f k x)
      matrixAverageUltrafilter (countableMatrixAverage e c hi ho f x) :=
  (Classical.choose_spec (matrix_average_limit_exists e c hi ho f)).2 x

lemma countableMatrixAverage_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f g : Cochain M n) :
    countableMatrixAverage e c hi ho (f + g) = countableMatrixAverage e c hi ho f + countableMatrixAverage e c hi ho g := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho (f + g) x)
  simpa only [matrixSectionAverage_add, add_apply] using predual_tendsto_add e
    (countableMatrixAverage_tendsto e c hi ho f x) (countableMatrixAverage_tendsto e c hi ho g x)

lemma countableMatrixAverage_smul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (z : ℂ) (f : Cochain M n) :
    countableMatrixAverage e c hi ho (z • f) = z • countableMatrixAverage e c hi ho f := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho (z • f) x)
  simpa only [matrixSectionAverage_smul, smul_apply] using predual_tendsto_smul e
    (countableMatrixAverage_tendsto e c hi ho f x) z

def countableMatrixAverageCLM (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (n : ℕ) :
    Cochain M n →L[ℂ] Cochain M n :=
  LinearMap.mkContinuous
    { toFun := countableMatrixAverage e c hi ho
      map_add' := countableMatrixAverage_add e c hi ho
      map_smul' := countableMatrixAverage_smul e c hi ho }
    1 (fun f => by
      change ‖countableMatrixAverage e c hi ho f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using countableMatrixAverage_norm e c hi ho f)

variable [CompleteSpace X]

lemma countableMatrixAverage_multimodular (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    MultimodularOver (countableMatrixAlgebra c) (countableMatrixAverage e c hi ho f) := by
  apply multimodular_of_matrixUnits c hi ho
  intro i j
  apply multimodularAt_of_predualTendsto e (matrixSectionAverage c hi ho f)
    (countableMatrixAverage e c hi ho f) _ (countableMatrixAverage_tendsto e c hi ho f)
  apply Ultrafilter.of_le atTop
  filter_upwards [eventually_gt_atTop (max i j)] with k hk
  exact matrixSectionAverage_module c hi ho f k
    ⟨i, lt_of_le_of_lt (le_max_left i j) hk⟩ ⟨j, lt_of_le_of_lt (le_max_right i j) hk⟩

lemma countableMatrixAverage_differential (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1)) :
    countableMatrixAverage e c hi ho (differential f) = differential (countableMatrixAverage e c hi ho f) := by
  ext x
  apply predual_tendsto_unique e (countableMatrixAverage_tendsto e c hi ho (differential f) x)
  simpa only [matrixSectionAverage_differential, differential_apply] using
    predual_tendsto_differential_of_predual e (countableMatrixAverage_tendsto e c hi ho f) x

lemma countableMatrixAverage_cocycle (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) :
    ∀ x, differentialValue (countableMatrixAverage e c hi ho f) x = 0 := by
  have hd : differential f = 0 := by
    ext x
    simpa only [differential_apply, zero_apply] using hf x
  have he := countableMatrixAverage_differential e c hi ho f
  rw [hd, show countableMatrixAverage e c hi ho (0 : Cochain M (n + 2)) = 0 from
    map_zero (countableMatrixAverageCLM e c hi ho (n + 2))] at he
  intro x
  simpa only [differential_apply, zero_apply] using
    congrArg (fun F : Cochain M (n + 2) => F x) he.symm

variable [PartialOrder M] [StarOrderedRing M]

theorem primitive_of_countableMatrixAverage [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = countableMatrixAverage e c hi ho f x :=
  primitive_of_algebraic_matrix_multimodular e hno c hi ho ht _
    (countableMatrixAverage_multimodular e c hi ho f) (countableMatrixAverage_cocycle e c hi ho f hf)

end BoundedHochschild.KadisonRingrose

end

end OAI

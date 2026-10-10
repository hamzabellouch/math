import OAI.Analysis.BoundedHochschild.CountableMatrixBarOperators
import OAI.Analysis.BoundedHochschild.CochainLimitDifferential

namespace OAI

/-! Passage to the weak-star limit for the bar-operator identity.
This module proves convergence of the defects; it does not assert that the
finite-group defects vanish. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def matrixSectionBarDefect (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (k : ℕ) : Cochain M (n + 1) :=
  differential (matrixSectionBarOperator c hi ho f k) +
    matrixSectionBarOperator c hi ho (differential f) k -
      (f - matrixSectionAverage c hi ho f k)

def countableMatrixBarDefect (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) : Cochain M (n + 1) :=
  differential (countableMatrixBarOperator e c hi ho f) +
    countableMatrixBarOperator e c hi ho (differential f) -
      (f - countableMatrixAverage e c hi ho f)

lemma countableMatrixBarDefect_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1)) (x : Fin (n + 1) → M) :
    PredualTendsto e (fun k => matrixSectionBarDefect c hi ho f k x)
      matrixAverageUltrafilter (countableMatrixBarDefect e c hi ho f x) := by
  have hd := predual_tendsto_differential_of_predual e
    (countableMatrixBarOperator_tendsto e c hi ho f) x
  have hH := countableMatrixBarOperator_tendsto e c hi ho (differential f) x
  have hP := predual_tendsto_sub e
    (predual_tendsto_const e (f x) (matrixAverageUltrafilter : Filter ℕ))
    (countableMatrixAverage_tendsto e c hi ho f x)
  simpa only [matrixSectionBarDefect, countableMatrixBarDefect,
    add_apply, sub_apply, differential_apply] using
      predual_tendsto_sub e (predual_tendsto_add e hd hH) hP

/-- An eventually vanishing finite-section defect has zero weak-star limit.
The finite algebraic identity is a separate obligation. -/
lemma countableMatrixBarDefect_eq_zero_of_eventually
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 1))
    (h : ∀ᶠ k in (matrixAverageUltrafilter : Filter ℕ),
      matrixSectionBarDefect c hi ho f k = 0) :
    countableMatrixBarDefect e c hi ho f = 0 := by
  ext x
  apply predual_tendsto_unique e (countableMatrixBarDefect_tendsto e c hi ho f x)
  apply predualTendsto_congr_eventually e _ (predual_tendsto_const e 0 _)
  filter_upwards [h] with k hk
  simp only [hk, zero_apply]

end BoundedHochschild.KadisonRingrose

end

end OAI

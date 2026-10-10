import OAI.Analysis.BoundedHochschild.MatrixBarLimits
import OAI.Analysis.BoundedHochschild.FiniteBarHomotopy

namespace OAI

/-! The explicit countable matrix average induces the identity in bounded
Hochschild cohomology. The uniform finite-group bar bounds allow its
homotopy to pass through the fixed weak-star ultralimit. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem countableMatrixBarOperator_homotopy (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 2)) :
    differential (countableMatrixBarOperator e c hi ho f) +
      countableMatrixBarOperator e c hi ho (differential f) =
        f - countableMatrixAverage e c hi ho f := by
  have hz : countableMatrixBarDefect e c hi ho f = 0 := by
    apply countableMatrixBarDefect_eq_zero_of_eventually
    filter_upwards [] with k
    unfold matrixSectionBarDefect matrixSectionBarOperator matrixSectionAverage
    rw [finiteGroupBarOperator_homotopy, sub_self]
  exact sub_eq_zero.mp hz

theorem countableMatrixBarOperator_cocycle (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) {n : ℕ}
    (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    differential (countableMatrixBarOperator e c hi ho f) =
      f - countableMatrixAverage e c hi ho f := by
  have hd : differential f = 0 := by
    ext x
    simpa only [differential_apply, zero_apply] using hf x
  have hzero : countableMatrixBarOperator e c hi ho (0 : Cochain M (n + 3)) = 0 :=
    map_zero (countableMatrixBarOperatorCLM e c hi ho (n + 2))
  have h := countableMatrixBarOperator_homotopy e c hi ho f
  simpa only [hd, hzero, add_zero] using h

end BoundedHochschild.KadisonRingrose

end

end OAI

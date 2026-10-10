import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

namespace SeymourSecondNeighborhood

variable {I J K : Type*} [Fintype I] [Fintype J] [Field K]

omit [Fintype I] in
private theorem matrix_rank_add_le (B C : Matrix I J K) :
    (B + C).rank ≤ B.rank + C.rank := by
  have hadd : (B + C).mulVecLin = B.mulVecLin + C.mulVecLin :=
    LinearMap.ext fun x => Matrix.add_mulVec B C x
  change Module.finrank K (LinearMap.range (B + C).mulVecLin) ≤
    Module.finrank K (LinearMap.range B.mulVecLin) +
      Module.finrank K (LinearMap.range C.mulVecLin)
  rw [hadd]
  exact (Submodule.finrank_mono
    (LinearMap.range_add_le B.mulVecLin C.mulVecLin)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_le_vertexCover_card (A : Matrix I J K) (s : Finset I) (t : Finset J)
    (hcover : ∀ i j, A i j ≠ 0 → i ∈ s ∨ j ∈ t) :
    A.rank ≤ s.card + t.card := by
  classical
  let B : Matrix I J K := fun i j => if i ∈ s then A i j else 0
  let C : Matrix I J K := fun i j => if i ∈ s then 0 else A i j
  have hsum : A = B + C := by
    ext i j
    change A i j = B i j + C i j
    by_cases hi : i ∈ s <;> simp [B, C, hi]
  have hB : B.rank ≤ s.card := by
    apply Matrix.rank_le_card_of_support_subset B s
    rw [Function.support_subset_iff']
    intro i hi
    change i ∉ s at hi
    funext j
    change (if i ∈ s then A i j else 0) = 0
    simp [hi]
  have hC : C.transpose.rank ≤ t.card := by
    apply Matrix.rank_le_card_of_support_subset C.transpose t
    rw [Function.support_subset_iff']
    intro j hj
    change j ∉ t at hj
    funext i
    change (if i ∈ s then 0 else A i j) = 0
    by_cases hi : i ∈ s
    · simp [hi]
    · have hA : A i j = 0 := by
        by_contra h
        exact (hcover i j h).elim hi hj
      simp [hi, hA]
  calc
    A.rank = (B + C).rank := congrArg Matrix.rank hsum
    _ ≤ B.rank + C.rank := matrix_rank_add_le B C
    _ ≤ s.card + t.card := add_le_add hB (by simpa only [Matrix.rank_transpose] using hC)

end SeymourSecondNeighborhood

end OAI

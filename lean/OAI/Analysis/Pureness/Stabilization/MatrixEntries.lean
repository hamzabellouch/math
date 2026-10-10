import OAI.Analysis.Pureness.Stabilization.MatrixSystem

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem matrixInclusion_entry_inside {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) (i j : Fin n) :
    matrixInclusion h M (Fin.castLE h i) (Fin.castLE h j) = M i j := by
  change matrixPad h M (Fin.castLE h i) (Fin.castLE h j) = M i j
  induction m, h using Nat.le_induction with
  | base => rw [matrixPad_self]; rfl
  | succ m h ih =>
    rw [matrixPad_succ h]
    change matrixSuccessor m (matrixPad h M) (Fin.castLE h i).castSucc (Fin.castLE h j).castSucc = M i j
    rw [matrixSuccessor_apply_castSucc,ih]

theorem matrixInclusion_entry_outside {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n)
    (i j : Fin m) (hij : n ≤ i.val ∨ n ≤ j.val) : matrixInclusion h M i j = 0 := by
  change matrixPad h M i j = 0
  induction m, h using Nat.le_induction with
  | base => rcases hij with hi | hj <;> omega
  | succ m h ih =>
    rw [matrixPad_succ h]
    revert hij
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro _; simp
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _; simp
      · intro hij
        rw [matrixSuccessor_apply_castSucc]
        exact ih i j hij

theorem matrixInclusion_entry {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) (i j : Fin m) :
    matrixInclusion h M i j =
      if hi : i.val < n then if hj : j.val < n then M ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0 else 0 := by
  split_ifs with hi hj
  · exact matrixInclusion_entry_inside h M ⟨i.val,hi⟩ ⟨j.val,hj⟩
  · exact matrixInclusion_entry_outside h M i j (Or.inr (Nat.le_of_not_gt hj))
  · exact matrixInclusion_entry_outside h M i j (Or.inl (Nat.le_of_not_gt hi))
end CuntzTrace

end

end OAI

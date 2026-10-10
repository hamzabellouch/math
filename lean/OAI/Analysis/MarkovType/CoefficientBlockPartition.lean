import OAI.Analysis.MarkovType.CoefficientConsecutiveBlocks
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {n m : ℕ}

omit sectionNormedSpaceℝE in
theorem consecutiveBlocks_eq_prefix_sub [NormedSpace ℝ E] (x : Fin n → E)
    (cuts : Fin (m + 1) → ℕ) (hcuts : Monotone cuts) (j : Fin m) :
    consecutiveBlocks x cuts j =
      (∑ i : Fin n, if i.val < cuts j.succ then x i else 0) -
        ∑ i : Fin n, if i.val < cuts j.castSucc then x i else 0 := by
  have hstep : cuts j.castSucc ≤ cuts j.succ :=
    hcuts (show j.castSucc ≤ j.succ from Nat.le_succ j.val)
  unfold consecutiveBlocks
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hlo : i.val < cuts j.castSucc
  · have hhi : i.val < cuts j.succ := hlo.trans_le hstep
    simp [hlo, hhi, not_le_of_gt hlo]
  · have hlo' : cuts j.castSucc ≤ i.val := Nat.le_of_not_gt hlo
    simp [hlo, hlo']

theorem sum_consecutiveBlocks (x : Fin n → E) (cuts : Fin (m + 1) → ℕ)
    (hcuts : Monotone cuts) (hfirst : cuts 0 = 0)
    (hlast : cuts (Fin.last m) = n) :
    (∑ j : Fin m, consecutiveBlocks x cuts j) = ∑ i : Fin n, x i := by
  let cutSum : Fin (m + 1) → E := fun j =>
    ∑ i : Fin n, if i.val < cuts j then x i else 0
  have hblock (j : Fin m) :
      consecutiveBlocks x cuts j = cutSum j.succ - cutSum j.castSucc :=
    consecutiveBlocks_eq_prefix_sub x cuts hcuts j
  calc
    (∑ j : Fin m, consecutiveBlocks x cuts j) =
        (∑ j : Fin m, cutSum j.succ) - ∑ j : Fin m, cutSum j.castSucc := by
      simp_rw [hblock]
      exact Finset.sum_sub_distrib (s := Finset.univ)
        (fun j : Fin m => cutSum j.succ) (fun j : Fin m => cutSum j.castSucc)
    _ = cutSum (Fin.last m) - cutSum 0 := by
      apply (sub_eq_sub_iff_add_eq_add (a := ∑ j : Fin m, cutSum j.succ)).mpr
      calc
        (∑ j : Fin m, cutSum j.succ) + cutSum 0 =
            cutSum 0 + ∑ j : Fin m, cutSum j.succ := add_comm _ _
        _ = ∑ j : Fin (m + 1), cutSum j := (Fin.sum_univ_succ cutSum).symm
        _ = (∑ j : Fin m, cutSum j.castSucc) + cutSum (Fin.last m) :=
          Fin.sum_univ_castSucc cutSum
        _ = cutSum (Fin.last m) + ∑ j : Fin m, cutSum j.castSucc := add_comm _ _
    _ = ∑ i : Fin n, x i := by simp [cutSum, hfirst, hlast]

end MarkovSuperreflexivity

end OAI

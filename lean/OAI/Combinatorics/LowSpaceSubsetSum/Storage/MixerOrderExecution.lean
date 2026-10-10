import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationIntegerParameters

namespace OAI

/-! # Three comparisons for the stable mixer order

Only strict count inversions are exchanged. Equal counts retain the original
index order, exactly as in the lexicographic mathematical sorting convention.
-/

namespace LowSpaceSubsetSum.MixerOrderExecution

def sort (counts : Fin 3 → ℕ) : Equiv.Perm (Fin 3) :=
  if counts 0 < counts 1 then
    if counts 0 < counts 2 then
      if counts 1 < counts 2 then Equiv.swap 0 2
      else (Equiv.swap 1 2).trans (Equiv.swap 0 1)
    else Equiv.swap 0 1
  else
    if counts 1 < counts 2 then
      if counts 0 < counts 2 then (Equiv.swap 0 1).trans (Equiv.swap 1 2)
      else Equiv.swap 1 2
    else Equiv.refl _

theorem sort_value (counts : Fin 3 → ℕ) : sort counts = mixerOrderFromCounts counts := by
  unfold sort
  split_ifs <;> apply Tuple.eq_sort_iff.mpr <;> constructor
  all_goals
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Equiv.swap_apply_def] <;> omega

def run (counts : Vector ℕ 3) : Vector (Fin 3) 3 × ℕ :=
  (Vector.ofFn (sort (fun i => counts[i.val])), 40)

theorem run_value (counts : Vector ℕ 3) (i : Fin 3) :
    (run counts).1[i.val] = mixerOrderFromCounts (fun j => counts[j.val]) i := by
  simp only [run, Vector.getElem_ofFn, sort_value]

theorem run_work (counts : Vector ℕ 3) : (run counts).2 ≤ 40 := le_rfl

end LowSpaceSubsetSum.MixerOrderExecution

end OAI

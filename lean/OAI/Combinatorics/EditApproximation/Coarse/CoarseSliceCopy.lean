import OAI.Combinatorics.EditApproximation.Coarse.CoarseRangeCopy
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLeaves

namespace OAI

namespace EditApproximation

theorem coarseRangeCopyWithWork_slice (input : List ℕ) (lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ input.length) :
    (coarseRangeCopyWithWork (fun i => input[i]?.getD 0) lo (hi - lo)).1 = substring input lo hi := by
  rw [coarseRangeCopyWithWork_value]
  apply List.ext_getElem
  · simp only [List.length_ofFn, substring, List.length_take, List.length_drop]
    rw [min_eq_left hhi]
  · intro i hi1 hi2
    have hil : i < hi - lo := by simpa only [List.length_ofFn] using hi1
    have hip : lo + i < input.length := by omega
    simp only [List.getElem_ofFn, substring, List.getElem_take, List.getElem_drop,
      List.getElem?_eq_getElem hip, Option.getD_some]

theorem coarseRangeCopyWithWork_input_cost (input : List ℕ) (lo hi A S : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ input.length) (haddress : Nat.size input.length ≤ A)
    (hsymbol : ∀ a ∈ input, Nat.size a ≤ S) :
    (coarseRangeCopyWithWork (fun i => input[i]?.getD 0) lo (hi - lo)).2 ≤
      (hi - lo + 1) * (40 * (A + 1) + S) := by
  apply coarseRangeCopyWithWork_cost _ input.length A S
  · intro i hi
    exact (Nat.size_le_size hi).trans haddress
  · intro i hi
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact hsymbol _ (List.getElem_mem hi)
  · omega

end EditApproximation

end OAI

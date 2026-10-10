import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryInputs
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition

namespace OAI

/-! Cost of generating the earlier-history input list from child grids.
The bound counts the actual nested lists before duplicate removal. -/

namespace EditApproximation

theorem arithmeticFlatMapWithWork_length {α β : Type*} (f : α → List β × ℕ)
    (xs : List α) (L : ℕ) (hL : ∀ x ∈ xs, (f x).1.length ≤ L) :
    (arithmeticFlatMapWithWork f xs).1.length ≤ xs.length * L := by
  induction xs with
  | nil => simp only [arithmeticFlatMapWithWork, List.length_nil, Nat.zero_mul, le_rfl]
  | cons x xs ih =>
    have hx := hL x List.mem_cons_self
    have ht := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    simp only [arithmeticFlatMapWithWork, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction

section History
variable {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P history : ℕ)
  (representatives : List (ℕ × TargetInterval ny)) (G C : ℕ)
  (hgrid : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).1.length ≤ G)
  (hwork : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).2 ≤ C)

private def historyChildRun (br : ℕ × TargetInterval ny) (i : Fin M) :=
  let states := wideChildGridWithWork parent br.2 br.1 P i
  let times := arithmeticFlatMapWithWork (fun t =>
    arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1) (List.range history)
  (times.1, states.2 + times.2 + history + 2)

include hgrid hwork in
private theorem historyChildRun_bounds (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives)
    (i : Fin M) :
    (historyChildRun M parent P history br i).1.length ≤ history * G ∧
    (historyChildRun M parent P history br i).2 ≤ C + history * (5 * G + 3) + history + 2 := by
  let states := wideChildGridWithWork parent br.2 br.1 P i
  have hs : states.1.length ≤ G := hgrid br hbr i
  have hc : states.2 ≤ C := hwork br hbr i
  have hlen (t : ℕ) :
      (arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1).1.length ≤ G := by
    simpa only [arithmeticMapWithWork_value, List.length_map] using hs
  have hcost (t : ℕ) :
      (arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1).2 ≤ 4 * G := by
    have h := arithmeticMapWithWork_cost (fun r => ((i, t, r), 1)) states.1 1 (fun _ _ => le_rfl)
    simpa only [Nat.reduceAdd, Nat.mul_comm] using h.trans (Nat.mul_le_mul_right 4 hs)
  have hl := arithmeticFlatMapWithWork_length
    (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1)
    (List.range history) G (fun t _ => hlen t)
  have hw := arithmeticFlatMapWithWork_cost
    (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1)
    (List.range history) (4 * G) G (fun t _ => hcost t) (fun t _ => hlen t)
  simp only [List.length_range] at hl hw
  refine ⟨hl, ?_⟩
  change states.2 + (arithmeticFlatMapWithWork
    (fun t => arithmeticMapWithWork (fun r => ((i, t, r), 1)) states.1)
    (List.range history)).2 + history + 2 ≤ _
  have heq : 4 * G + G + 3 = 5 * G + 3 := by omega
  rw [heq] at hw
  omega

include hgrid hwork in
theorem queryRawHistoryInputsWithWork_bounds :
    (queryRawHistoryInputsWithWork M parent P history representatives).1.length ≤
      representatives.length * (M * (history * G)) ∧
    (queryRawHistoryInputsWithWork M parent P history representatives).2 ≤
      representatives.length *
        (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) +
          M * (history * G) + 3) + M + 1 := by
  let run := fun br : ℕ × TargetInterval ny => arithmeticFlatMapWithWork (historyChildRun M parent P history br) (List.finRange M)
  have one (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) :
      (run br).1.length ≤ M * (history * G) ∧
      (run br).2 ≤ M * (C + history * (5 * G + 3) + history + 2 + history * G + 3) := by
    have hl := arithmeticFlatMapWithWork_length (historyChildRun M parent P history br)
      (List.finRange M) (history * G)
      (fun i _ => (historyChildRun_bounds M parent P history representatives G C hgrid hwork br hbr i).1)
    have hw := arithmeticFlatMapWithWork_cost (historyChildRun M parent P history br)
      (List.finRange M) (C + history * (5 * G + 3) + history + 2) (history * G)
      (fun i _ => (historyChildRun_bounds M parent P history representatives G C hgrid hwork br hbr i).2)
      (fun i _ => (historyChildRun_bounds M parent P history representatives G C hgrid hwork br hbr i).1)
    simpa only [List.length_finRange] using And.intro hl hw
  have hl := arithmeticFlatMapWithWork_length run representatives (M * (history * G))
    (fun br hbr => (one br hbr).1)
  have hw := arithmeticFlatMapWithWork_cost run representatives
    (M * (C + history * (5 * G + 3) + history + 2 + history * G + 3)) (M * (history * G))
    (fun br hbr => (one br hbr).2) (fun br hbr => (one br hbr).1)
  exact ⟨hl, Nat.add_le_add_right (Nat.add_le_add_right hw M) 1⟩

end History
end BinaryFraction
end EditApproximation

end OAI

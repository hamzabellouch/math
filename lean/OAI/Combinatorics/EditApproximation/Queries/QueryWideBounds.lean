import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryOrderBounds

namespace OAI

/-! Band-buffer input construction has a polynomial counter in the
number of representatives, emitted child-grid cells and key width. -/

namespace EditApproximation.BinaryFraction

section Wide
variable {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx) (P : ℕ)
  (representatives : List (ℕ × TargetInterval ny)) (G C B : ℕ)
  (hM : Nat.size M ≤ B) (hny : Nat.size ny ≤ B)
  (hgrid : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).1.length ≤ G)
  (hwork : ∀ br ∈ representatives, ∀ i : Fin M,
    (wideChildGridWithWork parent br.2 br.1 P i).2 ≤ C)

include hM hny hgrid hwork in
theorem queryWideInputsWithWork_bounds :
    (queryWideInputsWithWork M parent P representatives).1.length ≤ representatives.length * (M * G) ∧
    (queryWideInputsWithWork M parent P representatives).2 ≤
      representatives.length * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) +
      (representatives.length * (M * G) + 1) ^ 2 * (24 * B + 12) + M + 2 := by
  let childRun := fun (br : ℕ × TargetInterval ny) (i : Fin M) =>
    let states := wideChildGridWithWork parent br.2 br.1 P i
    let labeled := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (labeled.1, states.2 + labeled.2 + 1)
  let run := fun br : ℕ × TargetInterval ny => arithmeticFlatMapWithWork (childRun br) (List.finRange M)
  let raw := arithmeticFlatMapWithWork run representatives
  have child (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) (i : Fin M) :
      (childRun br i).1.length ≤ G ∧ (childRun br i).2 ≤ C + 4 * G + 1 := by
    have hl := hgrid br hbr i
    have hw := hwork br hbr i
    have hc := arithmeticMapWithWork_cost (fun r => ((i, r), 1))
      (wideChildGridWithWork parent br.2 br.1 P i).1 1 (fun _ _ => le_rfl)
    constructor
    · simpa only [childRun, arithmeticMapWithWork_value, List.length_map] using hl
    · change (wideChildGridWithWork parent br.2 br.1 P i).2 +
        (arithmeticMapWithWork (fun r => ((i, r), 1))
          (wideChildGridWithWork parent br.2 br.1 P i).1).2 + 1 ≤ _
      simp only [Nat.reduceAdd] at hc
      have hh := hc.trans (Nat.mul_le_mul_right 4 hl)
      omega
  have one (br : ℕ × TargetInterval ny) (hbr : br ∈ representatives) :
      (run br).1.length ≤ M * G ∧ (run br).2 ≤ M * (C + 4 * G + 1 + G + 3) := by
    have hl := arithmeticFlatMapWithWork_length (childRun br) (List.finRange M) G
      (fun i _ => (child br hbr i).1)
    have hw := arithmeticFlatMapWithWork_cost (childRun br) (List.finRange M) (C + 4 * G + 1) G
      (fun i _ => (child br hbr i).2) (fun i _ => (child br hbr i).1)
    simpa only [List.length_finRange] using And.intro hl hw
  have hl : raw.1.length ≤ representatives.length * (M * G) :=
    arithmeticFlatMapWithWork_length run representatives (M * G) (fun br hb => (one br hb).1)
  have hw : raw.2 ≤ representatives.length * (M * (C + 4 * G + 1 + G + 3) + M * G + 3) :=
    arithmeticFlatMapWithWork_cost run representatives (M * (C + 4 * G + 1 + G + 3)) (M * G)
      (fun br hb => (one br hb).2) (fun br hb => (one br hb).1)
  have he := queryEraseWithWork_cost coordinateEqualWithWork (24 * B + 8)
    (fun a b => coordinateEqualWithWork_cost a b B hM hny) raw.1
  have hsq : (raw.1.length + 1) ^ 2 ≤ (representatives.length * (M * G) + 1) ^ 2 := by gcongr
  have he' := he.trans (Nat.mul_le_mul_right (24 * B + 8 + 4) hsq)
  simp only [Nat.add_assoc, Nat.reduceAdd] at he'
  have hu := (queryEraseWithWork_length coordinateEqualWithWork raw.1).trans hl
  refine ⟨hu, ?_⟩
  change raw.2 + (queryEraseWithWork coordinateEqualWithWork raw.1).2 + M + 2 ≤ _
  omega

end Wide
end EditApproximation.BinaryFraction

end OAI

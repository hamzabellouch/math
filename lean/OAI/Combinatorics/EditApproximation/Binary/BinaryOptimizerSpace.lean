import OAI.Combinatorics.EditApproximation.Binary.BinaryNumericSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRawOptimizer
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Fresh list cells and primitive call frames of the materialized Boolean
optimizer. Intermediate vectors may all remain live; the counters include
every optimizer iteration and every candidate score. -/

namespace EditApproximation



def vectorMapInvocations (d : ℕ) (invocations : Fin d → ℕ) : ℕ :=
  (∑ i, invocations i) + 3 * d + 1

theorem vectorMapAllocation_le_work {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (allocation : Fin d → ℕ) (h : ∀ i, allocation i ≤ (f i).2) :
    vectorMapAllocation d allocation ≤ (vectorMapWithWork d f).2 := by
  have hs := Finset.sum_le_sum (fun (i : Fin d) (_ : i ∈ Finset.univ) => h i)
  have he : ((Vector.ofFn f).map Prod.snd).toList.sum = ∑ i : Fin d, (f i).2 := by
    simp only [Vector.toList_map, Vector.toList_ofFn, List.map_ofFn, Function.comp_def,
      List.sum_ofFn]
  unfold vectorMapAllocation vectorMapWithWork
  dsimp only
  rw [he]
  omega

theorem vectorMapInvocations_le_work_add_one {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (invocations : Fin d → ℕ) (h : ∀ i, invocations i ≤ (f i).2) :
    vectorMapInvocations d invocations ≤ (vectorMapWithWork d f).2 + 1 := by
  have hs := Finset.sum_le_sum (fun (i : Fin d) (_ : i ∈ Finset.univ) => h i)
  have he : ((Vector.ofFn f).map Prod.snd).toList.sum = ∑ i : Fin d, (f i).2 := by
    simp only [Vector.toList_map, Vector.toList_ofFn, List.map_ofFn, Function.comp_def,
      List.sum_ofFn]
  unfold vectorMapInvocations vectorMapWithWork
  dsimp only
  rw [he]
  omega

namespace BinaryFraction



def gradientInvocations {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) : ℕ :=
  vectorMapInvocations d (gradientCellInvocations G linear point)

theorem gradientAllocation_le_work {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) :
    gradientAllocation G linear point ≤ (gradientWithWork G linear point).2 :=
  vectorMapAllocation_le_work d _ _ (gradientCellAllocation_le_work G linear point)

theorem gradientInvocations_le_work_add_one {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) :
    gradientInvocations G linear point ≤ (gradientWithWork G linear point).2 + 1 :=
  vectorMapInvocations_le_work_add_one d _ _ (gradientCellInvocations_le_work G linear point)



def scoredArgmaxInvocations {α : Type*} (score : α → BinaryFraction × ℕ)
    (invocations : α → ℕ) : List α → ℕ
  | [] => 1
  | a :: rest =>
    scoredArgmaxInvocations score invocations rest + invocations a +
      match (scoredArgmaxWithWork score rest).1 with
      | none => 1
      | some best => compareInvocations (score a).1 best.2 + 1

theorem scoredArgmaxAllocation_le_work {α : Type*} (score : α → BinaryFraction × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ a ∈ xs, allocation a ≤ (score a).2) :
    scoredArgmaxAllocation score allocation xs ≤ (scoredArgmaxWithWork score xs).2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [scoredArgmaxAllocation, scoredArgmaxWithWork]
    cases he : (scoredArgmaxWithWork score xs).1 with
    | none => dsimp only; omega
    | some best =>
      have hc := ltAllocation_le_work (score a).1 best.2
      change scoredArgmaxAllocation score allocation xs + allocation a +
        (ltAllocation (score a).1 best.2 + 1) ≤
          (scoredArgmaxWithWork score xs).2 + (score a).2 +
            ((score a).1.ltWithWork best.2).2 + 2
      omega

theorem scoredArgmaxInvocations_le_work_add_one {α : Type*} (score : α → BinaryFraction × ℕ)
    (invocations : α → ℕ) (xs : List α) (h : ∀ a ∈ xs, invocations a ≤ (score a).2) :
    scoredArgmaxInvocations score invocations xs ≤ (scoredArgmaxWithWork score xs).2 + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [scoredArgmaxInvocations, scoredArgmaxWithWork]
    cases he : (scoredArgmaxWithWork score xs).1 with
    | none => dsimp only; omega
    | some best =>
      have hc := compareInvocations_le_work (score a).1 best.2
      change scoredArgmaxInvocations score invocations xs + invocations a +
        (compareInvocations (score a).1 best.2 + 1) ≤
          ((scoredArgmaxWithWork score xs).2 + (score a).2 +
            ((score a).1.ltWithWork best.2).2 + 2) + 1
      omega



def maximizerInvocations {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) : ℕ :=
  scoredArgmaxInvocations (dotWithWork gradient)
    (fun v => dotListInvocations gradient v (List.finRange d)) vertices + 1

theorem maximizerAllocation_le_work {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) :
    maximizerAllocation gradient vertices ≤ (maximizerWithWork gradient vertices).2 := by
  have h := scoredArgmaxAllocation_le_work (dotWithWork gradient)
    (fun v => dotListAllocation gradient v (List.finRange d)) vertices
    (fun v _ => dotListAllocation_le_work gradient v (List.finRange d))
  unfold maximizerAllocation maximizerWithWork
  dsimp only
  omega

theorem maximizerInvocations_le_work_add_one {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) :
    maximizerInvocations gradient vertices ≤ (maximizerWithWork gradient vertices).2 + 1 := by
  have h := scoredArgmaxInvocations_le_work_add_one (dotWithWork gradient)
    (fun v => dotListInvocations gradient v (List.finRange d)) vertices
    (fun v _ => dotListInvocations_le_work gradient v (List.finRange d))
  unfold maximizerInvocations maximizerWithWork
  dsimp only
  omega



def optimizerUpdateCellInvocations {d : ℕ} (step complement : BinaryFraction)
    (previous selected : Vector BinaryFraction d) (i : Fin d) : ℕ :=
  canonicalMulInvocations complement (previous.get i) + canonicalMulInvocations step (selected.get i) +
    canonicalAddInvocations (canonicalMulWithWork complement (previous.get i)).1
      (canonicalMulWithWork step (selected.get i)).1 + 1



def optimizerUpdateInvocations {d : ℕ} (j : ℕ) (previous selected : Vector BinaryFraction d) : ℕ :=
  let step := (divWithWork (nat 2) (nat (j + 2))).1
  let complement := (subWithWork one step).1
  divInvocations (nat 2) (nat (j + 2)) + subInvocations one step +
    vectorMapInvocations d (optimizerUpdateCellInvocations step complement previous selected) + 1

theorem optimizerUpdateAllocation_le_work {d : ℕ} (j : ℕ) (previous selected : Vector BinaryFraction d) :
    optimizerUpdateAllocation j previous selected ≤ (optimizerUpdateWithWork j previous selected).2 := by
  have h1 := divAllocation_le_work (nat 2) (nat (j + 2))
  have h2 := subAllocation_le_work one (divWithWork (nat 2) (nat (j + 2))).1
  have h3 := vectorMapAllocation_le_work d
    (fun i =>
      let first := canonicalMulWithWork (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)
      let second := canonicalMulWithWork (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)
      let total := canonicalAddWithWork first.1 second.1
      (total.1, first.2 + second.2 + total.2 + 4))
    (optimizerUpdateCellAllocation (divWithWork (nat 2) (nat (j + 2))).1
      (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 previous selected) (by
        intro i
        have hm1 := canonicalMulAllocation_le_work (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)
        have hm2 := canonicalMulAllocation_le_work (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)
        have ha := canonicalAddAllocation_le_work
          (canonicalMulWithWork (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)).1
          (canonicalMulWithWork (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)).1
        unfold optimizerUpdateCellAllocation
        dsimp only
        omega)
  unfold optimizerUpdateAllocation optimizerUpdateWithWork
  dsimp only at h3 ⊢
  omega

theorem optimizerUpdateInvocations_le_work {d : ℕ} (j : ℕ) (previous selected : Vector BinaryFraction d) :
    optimizerUpdateInvocations j previous selected ≤ (optimizerUpdateWithWork j previous selected).2 := by
  have h1 := divInvocations_le_work (nat 2) (nat (j + 2))
  have h2 := subInvocations_le_work one (divWithWork (nat 2) (nat (j + 2))).1
  have h3 := vectorMapInvocations_le_work_add_one d
    (fun i =>
      let first := canonicalMulWithWork (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)
      let second := canonicalMulWithWork (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)
      let total := canonicalAddWithWork first.1 second.1
      (total.1, first.2 + second.2 + total.2 + 4))
    (optimizerUpdateCellInvocations (divWithWork (nat 2) (nat (j + 2))).1
      (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 previous selected) (by
        intro i
        have hm1 := canonicalMulInvocations_le_work (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)
        have hm2 := canonicalMulInvocations_le_work (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)
        have ha := canonicalAddInvocations_le_work
          (canonicalMulWithWork (subWithWork one (divWithWork (nat 2) (nat (j + 2))).1).1 (previous.get i)).1
          (canonicalMulWithWork (divWithWork (nat 2) (nat (j + 2))).1 (selected.get i)).1
        unfold optimizerUpdateCellInvocations
        dsimp only
        omega)
  unfold optimizerUpdateInvocations optimizerUpdateWithWork
  dsimp only at h3 ⊢
  omega



def optimizerInvocations {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 =>
    let previous := (finiteOptimizerWithWork vertices linear G j).1
    let gradient := (gradientWithWork G linear previous).1
    let selected := (maximizerWithWork gradient vertices).1
    optimizerInvocations vertices linear G j + gradientInvocations G linear previous +
      maximizerInvocations gradient vertices + optimizerUpdateInvocations j previous selected + 1

theorem optimizerAllocation_le_work {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    optimizerAllocation vertices linear G K ≤ (finiteOptimizerWithWork vertices linear G K).2 := by
  induction K with
  | zero => exact Nat.le_succ _
  | succ K ih =>
    have hg := gradientAllocation_le_work G linear (finiteOptimizerWithWork vertices linear G K).1
    have hm := maximizerAllocation_le_work (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices
    have hu := optimizerUpdateAllocation_le_work K (finiteOptimizerWithWork vertices linear G K).1
      (maximizerWithWork (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices).1
    simp only [optimizerAllocation, finiteOptimizerWithWork]
    exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ih hg) hm) hu).trans
      (Nat.le_add_right _ 3)

theorem optimizerInvocations_le_work {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    optimizerInvocations vertices linear G K ≤ (finiteOptimizerWithWork vertices linear G K).2 := by
  induction K with
  | zero => simp only [optimizerInvocations, finiteOptimizerWithWork]; omega
  | succ K ih =>
    have hg := gradientInvocations_le_work_add_one G linear (finiteOptimizerWithWork vertices linear G K).1
    have hm := maximizerInvocations_le_work_add_one (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices
    have hu := optimizerUpdateInvocations_le_work K (finiteOptimizerWithWork vertices linear G K).1
      (maximizerWithWork (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices).1
    simp only [optimizerInvocations, finiteOptimizerWithWork]
    omega

end BinaryFraction
end EditApproximation

end OAI

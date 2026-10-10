import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tick

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryIteration

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

section Presentation

variable {F : Type*} [Field F] {SX SY SZ X Y Z : Type}
    [Fintype SX] [Fintype SY] [Fintype SZ]
    {source : Tensor F SX SY SZ} {target next : Tensor F X Y Z}

private def retarget (E : Execution source target) (h : target = next) :
    Execution source next where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map := {
    x := E.map.x
    y := E.map.y
    z := E.map.z
    coefficient := E.map.coefficient.trans h
  }

@[simp] private theorem retarget_copies (E : Execution source target) (h : target = next) :
    Fintype.card (retarget E h).Copies = Fintype.card E.Copies := rfl

end Presentation

variable {K : ℕ} (allocation : Allocation) (m : ℕ) (ε slack : ℝ)

abbrev ScheduleChoices := ∀ t : Fin (K + 2),
  AllFieldHistoryTick.Choices (K := K) (tick := t.val) allocation m ε slack

def Labels (InitialTag : Type)
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    (n : ℕ) → n ≤ K + 2 → Type
  | 0, _ => InitialTag
  | n + 1, hn =>
      Labels InitialTag chosen n (Nat.le_of_succ_le hn) ×
        AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)

instance labelsFintype (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    (n : ℕ) → (hn : n ≤ K + 2) →
      Fintype (Labels allocation m ε slack InitialTag chosen n hn)
  | 0, _ => inferInstanceAs (Fintype InitialTag)
  | n + 1, hn => by
      let := labelsFintype InitialTag chosen n (Nat.le_of_succ_le hn)
      exact inferInstanceAs (Fintype
        (Labels allocation m ε slack InitialTag chosen n (Nat.le_of_succ_le hn) ×
          AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)))

theorem card_labels (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    (n : ℕ) (hn : n ≤ K + 2) :
    Fintype.card (Labels allocation m ε slack InitialTag chosen n hn) =
      Fintype.card InitialTag * ∏ t : Fin n, ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) *
          (AllFieldGroupSelection.nativeCapacity (K := K) (tick := t.val) allocation - slack))⌋₊ := by
  induction n with
  | zero =>
      change Fintype.card InitialTag = Fintype.card InitialTag * 1
      exact (Nat.mul_one _).symm
  | succ n ih =>
      change Fintype.card
        (Labels allocation m ε slack InitialTag chosen n (Nat.le_of_succ_le hn) ×
          AllFieldHistoryTick.Tags allocation m ε slack (chosen ⟨n, hn⟩)) = _
      rw [Fintype.card_prod, AllFieldHistoryTick.card_tags, ih, Fin.prod_univ_castSucc]
      exact Nat.mul_assoc _ _ _

abbrev Tags (InitialTag : Type)
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :=
  Labels allocation m ε slack InitialTag chosen (K + 2) le_rfl

theorem card_tags (InitialTag : Type) [Fintype InitialTag]
    (chosen : ScheduleChoices (K := K) allocation m ε slack) :
    Fintype.card (Tags allocation m ε slack InitialTag chosen) =
      Fintype.card InitialTag * ∏ t : Fin (K + 2), ∏ _sigma : Placement,
        ⌊Real.exp ((m : ℝ) *
          (AllFieldGroupSelection.nativeCapacity (K := K) (tick := t.val) allocation - slack))⌋₊ :=
  card_labels allocation m ε slack InitialTag chosen (K + 2) le_rfl

variable (F : Type*) [Field F] (hε : 0 < ε)
    (hm : ∀ t : Fin (K + 2),
      AllFieldHistoryRecovery.minimumDilation (K := K) (tick := t.val) allocation ε ≤ m)
    (chosen : ScheduleChoices (K := K) allocation m ε slack)
    {InitialTag : Type} [Fintype InitialTag]
    (start : Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : InitialTag => stateTensor F (K := K) allocation m ε 0)))

def run : (n : ℕ) → (hn : n ≤ K + 2) →
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Labels allocation m ε slack InitialTag chosen n hn =>
        stateTensor F (K := K) allocation m ε n))
  | 0, _ => start
  | n + 1, hn =>
      let step := AllFieldHistoryTick.execution allocation m ε slack F hε
        (hm ⟨n, hn⟩) (chosen ⟨n, hn⟩)
      let operation := Execution.branchOperation
        (stateTensor F (K := K) allocation m ε n)
        (stateTensor F (K := K) allocation m ε (n + 1))
        (run n (Nat.le_of_succ_le hn)) step.copies_positive step.map
      retarget operation (by
        funext x y z
        simp only [Tensor.directSum]
        split_ifs <;> first | rfl | contradiction)

theorem run_copies (n : ℕ) (hn : n ≤ K + 2) :
    Fintype.card (run allocation m ε slack F hε hm chosen start n hn).Copies =
      Fintype.card start.Copies * ∏ t : Fin n,
        2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := t.val) allocation ε m) := by
  induction n with
  | zero =>
      change Fintype.card start.Copies = Fintype.card start.Copies * 1
      exact (Nat.mul_one _).symm
  | succ n ih =>
      rw [run]
      erw [retarget_copies]
      rw [Execution.branchOperation_copies, AllFieldHistoryTick.execution_copies,
        ih, Fin.prod_univ_castSucc]
      ring

def execution :
    Execution (cwSource F K (populationLength (K := K) allocation m))
      (Tensor.directSum (fun _ : Tags allocation m ε slack InitialTag chosen =>
        stateTensor F (K := K) allocation m ε (K + 2))) :=
  run allocation m ε slack F hε hm chosen start (K + 2) le_rfl

@[simp] theorem execution_copies :
    Fintype.card (execution allocation m ε slack F hε hm chosen start).Copies =
      Fintype.card start.Copies * ∏ t : Fin (K + 2),
        2 ^ (3 * AllFieldHistoryRecovery.shiftCount (K := K) (tick := t.val) allocation ε m) :=
  run_copies allocation m ε slack F hε hm chosen start (K + 2) le_rfl

end MatrixMultiplication.AllFieldHistoryIteration

end

end OAI

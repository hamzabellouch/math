import Mathlib.Tactic.FinCases
import OAI.Analysis.MutuallyUnbiased.Cubic.FiveCycle

namespace OAI

/-! A second finite presentation of the five-cycle classification.  A row has
two positive signs among four off-diagonal positions, hence six choices. -/

namespace MUB6

def fourChoices : Fin 6 → Fin 4 → Bool :=
  ![![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false],
    ![false, true, false, true], ![false, false, true, true]]

def offDiagonalIndex (i j : Fin 5) (h : i ≠ j) : Fin 4 :=
  ⟨if j.val < i.val then j.val else j.val - 1, by
    have hn : i.val ≠ j.val := fun e => h (Fin.ext e)
    split_ifs <;> omega⟩

def fiveRowChoice (i : Fin 5) (a : Fin 6) (j : Fin 5) : Bool :=
  if h : i = j then false else fourChoices a (offDiagonalIndex i j h)

def normalizedCodeGraph (a : Fin 5 → Fin 6) (i j : Fin 5) : Bool :=
  fiveRowChoice i (a i) j

theorem rowChoice_complete : ∀ (i : Fin 5) (f : Fin 5 → Bool),
    f i = false → (Finset.univ.filter (fun j => f j = true)).card = 2 →
      ∃ a, ∀ j, fiveRowChoice i a j = f j := by
  decide +kernel

def normalizedCodeOrthogonal (a : Fin 5 → Fin 6) : Prop :=
  ∀ i j, i ≠ j →
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧
      normalizedCodeGraph a i k = normalizedCodeGraph a j k)).card = 1

def normalizedCodeClassified (a : Fin 5 → Fin 6) : Prop :=
  normalizedCodeOrthogonal a →
    ∃ c, ∀ i j, normalizedCodeGraph a (fiveCycleOrder c i) (fiveCycleOrder c j) =
      canonicalFiveCycle i j

private theorem normalizedCodes_00 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_01 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_02 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_03 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_04 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_05 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![0, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_10 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_11 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_12 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_13 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_14 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_15 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![1, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_20 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_21 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_22 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_23 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_24 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_25 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![2, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_30 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_31 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_32 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_33 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_34 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_35 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![3, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_40 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_41 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_42 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_43 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_44 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_45 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![4, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_50 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 0, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_51 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 1, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_52 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 2, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_53 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 3, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_54 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 4, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

private theorem normalizedCodes_55 : ∀ (a2 a3 a4 : Fin 6),
    normalizedCodeClassified ![5, 5, a2, a3, a4] := by
  unfold normalizedCodeClassified normalizedCodeOrthogonal
  decide +kernel

theorem normalizedCodes_classified (a : Fin 5 → Fin 6) : normalizedCodeClassified a := by
  have h (a0 a1 a2 a3 a4 : Fin 6) : normalizedCodeClassified ![a0, a1, a2, a3, a4] := by
    fin_cases a0 <;> fin_cases a1
    · exact normalizedCodes_00 a2 a3 a4
    · exact normalizedCodes_01 a2 a3 a4
    · exact normalizedCodes_02 a2 a3 a4
    · exact normalizedCodes_03 a2 a3 a4
    · exact normalizedCodes_04 a2 a3 a4
    · exact normalizedCodes_05 a2 a3 a4
    · exact normalizedCodes_10 a2 a3 a4
    · exact normalizedCodes_11 a2 a3 a4
    · exact normalizedCodes_12 a2 a3 a4
    · exact normalizedCodes_13 a2 a3 a4
    · exact normalizedCodes_14 a2 a3 a4
    · exact normalizedCodes_15 a2 a3 a4
    · exact normalizedCodes_20 a2 a3 a4
    · exact normalizedCodes_21 a2 a3 a4
    · exact normalizedCodes_22 a2 a3 a4
    · exact normalizedCodes_23 a2 a3 a4
    · exact normalizedCodes_24 a2 a3 a4
    · exact normalizedCodes_25 a2 a3 a4
    · exact normalizedCodes_30 a2 a3 a4
    · exact normalizedCodes_31 a2 a3 a4
    · exact normalizedCodes_32 a2 a3 a4
    · exact normalizedCodes_33 a2 a3 a4
    · exact normalizedCodes_34 a2 a3 a4
    · exact normalizedCodes_35 a2 a3 a4
    · exact normalizedCodes_40 a2 a3 a4
    · exact normalizedCodes_41 a2 a3 a4
    · exact normalizedCodes_42 a2 a3 a4
    · exact normalizedCodes_43 a2 a3 a4
    · exact normalizedCodes_44 a2 a3 a4
    · exact normalizedCodes_45 a2 a3 a4
    · exact normalizedCodes_50 a2 a3 a4
    · exact normalizedCodes_51 a2 a3 a4
    · exact normalizedCodes_52 a2 a3 a4
    · exact normalizedCodes_53 a2 a3 a4
    · exact normalizedCodes_54 a2 a3 a4
    · exact normalizedCodes_55 a2 a3 a4
  have he : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact h _ _ _ _ _

end MUB6

end OAI

import OAI.Combinatorics.LowSpaceSubsetSum.Separators.PreparedIncidenceCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorFlow

namespace OAI

/-! # Prepaid construction of the shared separator context

The scalar guard precedes every incidence-row allocation. Its successful
branch evaluates the new table builder once and retains only its blocks.
-/

namespace LowSpaceSubsetSum.BudgetedIncidencePreparation

open StoredSeparatorCheck BudgetedSeparatorCall

variable {n g : ℕ}

def charge (g : ℕ) : ℕ := 1000 * 2 ^ (2 * g) + 64 * (g + 5) + 1

def execute (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) :
    Outcome (List (Block n g)) × ℕ :=
  if charge g ≤ budget then
    let out := PreparedIncidenceCells.prepare rows families hsize
    ((some (out.1.1, budget - charge g), out.1.2 + 1), out.2 + 8)
  else ((none, 1), 8)

theorem outcome_eq (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) :
    (execute rows families hsize budget).1 =
      BudgetedSeparatorCall.run (charge g)
        (fun _ => (PreparedIncidenceCells.prepare rows families hsize).1) budget := by
  unfold execute BudgetedSeparatorCall.run
  split <;> rfl

theorem prepared_charge (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) :
    (PreparedIncidenceCells.prepare rows families hsize).1.2 + 1 ≤ charge g := by
  have h := PreparedIncidenceCells.prepare_work rows families hsize
  unfold charge
  omega

theorem account (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) :
    BudgetedSeparatorFlow.Account budget (execute rows families hsize budget).1 := by
  rw [outcome_eq]
  exact ⟨BudgetedSeparatorCall.work _ _ _ (prepared_charge rows families hsize),
    fun _ _ h => BudgetedSeparatorCall.spent _ _ _ (prepared_charge rows families hsize) _ _ h⟩

theorem complete (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ)
    (hb : charge g ≤ budget) :
    (execute rows families hsize budget).1.1 =
      some ((PreparedSeparatorContext.prepare rows families hsize).1, budget - charge g) := by
  simp only [execute, ite_eq_left hb, PreparedIncidenceCells.prepare_value]

theorem value (rows : Fin 4 → Vector (Fin n) g)
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ)
    (blocks : List (Block n g)) (remaining : ℕ)
    (h : (execute rows families hsize budget).1.1 = some (blocks, remaining)) :
    blocks = (PreparedSeparatorContext.prepare rows families hsize).1 ∧
      budget = remaining + charge g := by
  have hh := h
  rw [outcome_eq] at hh
  obtain ⟨hv, hr, hc⟩ := BudgetedSeparatorCall.value _ _ _ _ _ hh
  exact ⟨hv.trans (PreparedIncidenceCells.prepare_value rows families hsize), by omega⟩

theorem charge_scale (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C) : charge g ≤ inputScale I ^ 2 * C := by
  have hCpos : 1 ≤ C := (Nat.one_le_two_pow).trans hC
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 1000 + 64 * (g + 5) + 1 ≤ inputScale I ^ 2 := by
    nlinarith only [hu, hg, hn]
  have hm := Nat.mul_le_mul_left (64 * (g + 5) + 1) hCpos
  have hp := Nat.mul_le_mul_left 1000 hC
  calc
    charge g ≤ (1000 + 64 * (g + 5) + 1) * C := by unfold charge; nlinarith only [hm, hp]
    _ ≤ inputScale I ^ 2 * C := Nat.mul_le_mul_right C hcoef

theorem cells_with_inputs (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2 ^ (2 * g) ≤ C)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) :
    (execute rows families hsize budget).2 + PreparedIncidenceCells.retainedInputs families ≤
      inputScale I ^ 3 * (C + 1) := by
  have h := PreparedIncidenceCells.prepare_cells_with_inputs I hn hg C hC rows families hsize
  have hu : 2 ≤ inputScale I := by unfold inputScale; omega
  have hpow : inputScale I ^ 2 ≤ inputScale I ^ 3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h8 : 8 ≤ inputScale I ^ 3 := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ inputScale I ^ 3 := Nat.pow_le_pow_left hu 3
  have hlocal : (execute rows families hsize budget).2 +
      PreparedIncidenceCells.retainedInputs families ≤ inputScale I ^ 2 * C + 8 := by
    unfold execute
    split <;> dsimp only <;> omega
  calc
    _ ≤ inputScale I ^ 2 * C + 8 := hlocal
    _ ≤ inputScale I ^ 3 * C + inputScale I ^ 3 :=
      Nat.add_le_add (Nat.mul_le_mul_right C hpow) h8
    _ = _ := by ring

end LowSpaceSubsetSum.BudgetedIncidencePreparation

end OAI

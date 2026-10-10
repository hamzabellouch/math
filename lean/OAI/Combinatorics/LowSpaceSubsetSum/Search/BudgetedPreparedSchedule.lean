import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedScheduleAccount
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedScheduleWatchdog
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedIncidencePreparation

namespace OAI

/-! # Prepaid shared tables followed by the concrete residue schedule

The constructor's resulting blocks are passed directly to the schedule.
There is one budget, including initialization and all failed buckets.
-/

namespace LowSpaceSubsetSum.BudgetedPreparedSchedule

open BudgetedSeparatorFlow

variable {n g : ℕ}

def run (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ) :=
  bind (BudgetedIncidencePreparation.execute rows families hsize budget).1
    (fun blocks left => BudgetedSchedule.run D F hF B blocks D.target left)

theorem value (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run D F hF B rows families hsize budget).1 = some (v, rest)) :
    v = D.run B (fun i => (families i).map SeparatorStoredMasks.decode) := by
  obtain ⟨blocks, left, hf, he⟩ := (bind_eq_some _ _ _ _).mp h
  have hv := (BudgetedIncidencePreparation.value rows families hsize budget blocks left hf).1
  rw [hv] at he
  exact BudgetedSchedule.value D F hF B rows hrows families hsize D.target rfl left v rest he

theorem complete (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ)
    (hb : BudgetedIncidencePreparation.charge g + BudgetedSchedule.allowance D F hF B
      (fun i => (families i).map SeparatorStoredMasks.decode) ≤ budget) :
    ∃ v rest, (run D F hF B rows families hsize budget).1 = some (v, rest) := by
  have hc : BudgetedIncidencePreparation.charge g ≤ budget := by omega
  have hf := BudgetedIncidencePreparation.complete rows families hsize budget hc
  obtain ⟨v, rest, he⟩ := BudgetedSchedule.complete D F hF B hn hg rows hrows families hsize
    D.target rfl (budget - BudgetedIncidencePreparation.charge g) (by omega)
  exact ⟨v, rest, bind_complete _ _ _ _ _ _ hf he⟩

theorem account (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g) (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ)
    (hn : 10000 ≤ n)
    (hraw : ∀ side i, (D.leaves side i).occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2 ^ n)
    (hcopy : ∀ z side (P : StoredRestriction n), (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D.parentData side z with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B) :
    Account budget (run D F hF B rows families hsize budget) := by
  apply bind_account
  · exact BudgetedIncidencePreparation.account rows families hsize budget
  · intro blocks left _
    exact BudgetedSchedule.account D F hF B blocks left D.target hn hraw hC hcopy

theorem accepts_of_core (D : RepresentationScheduleData n g) (F : IndexedMask n)
    (hF : F.semantic = D.signs) (B : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (hwidth : 2 ^ (2 * g) ≤ 2 ^ ((n + 1) / 2))
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (hcore : (D.coreUnits B (fun i => (families i).map SeparatorStoredMasks.decode) : ℝ) ≤
      (inputScale D.input : ℝ) ^ 410 * (2 : ℝ) ^ ((n + 1) / 2))
    (hyes : D.run B (fun i => (families i).map SeparatorStoredMasks.decode) = true) :
    ∃ rest, (run D F hF B rows families hsize (2 * trialWatchdog D.input)).1 =
      some (true, rest) := by
  have hcharge := BudgetedIncidencePreparation.charge_scale D.input hn hg
    (2 ^ ((n + 1) / 2)) hwidth
  have hu : 1 ≤ inputScale D.input := by unfold inputScale; omega
  have hp : inputScale D.input ^ 2 ≤ inputScale D.input ^ 500 :=
    pow_le_pow_right' hu (by omega : 2 ≤ 500)
  have hc : BudgetedIncidencePreparation.charge g ≤ trialWatchdog D.input :=
    hcharge.trans (Nat.mul_le_mul_right _ hp)
  have hs := BudgetedSchedule.allowance_le_watchdog D F hF hn B _ hcore
  obtain ⟨v, rest, he⟩ := complete D F hF B hn hg rows hrows families hsize
    (2 * trialWatchdog D.input) (by omega)
  have hv := value D F hF B rows hrows families hsize _ v rest he
  rw [hyes] at hv
  exact ⟨rest, by simpa only [hv] using he⟩

end LowSpaceSubsetSum.BudgetedPreparedSchedule

end OAI

import OAI.NumberTheory.Ostmann.Construction.InitialCellScheduleEquiv
import OAI.NumberTheory.Ostmann.Construction.InitialMovingSmallPermutation

namespace OAI

/-! # The selected original priors in compensation order -/
namespace Ostmann
open scoped Classical

noncomputable def scheduledRegularPrior {A : Type} (cell : ℕ → A → ℝ)
    (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    MovingRegularSlot n (scheduledSmallLength cs) m → A → ℝ :=
  fun i => Sum.elim (fun j => cell (scheduledSmallCell top cs j)) (fun _ => bulk) i.2

theorem initialMovingRegularPrior_cell_reindex {A : Type}
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (b : ℕ) :
    let cells := initialSmallCellList top cs
    ∃ e : Fin (cells.length + cells.length) ≃ Fin (scheduledSmallLength cs),
      initialMovingRegularPrior b cells.length (fun _ => bulk) (fun i => cell (cells.get i)) =
        fun i => scheduledRegularPrior cell bulk top cs 0 (b + b)
          (movingSmallSlotEquiv 0 (b + b) e i) := by
  intro cells
  obtain ⟨e, he⟩ := initialCellSchedule_index_equiv top cs
  refine ⟨e, ?_⟩
  funext i
  rcases i with ⟨j, i | i⟩
  · change Fin.append (fun i => cell (cells.get i)) (fun i => cell (cells.get i)) i =
      cell (scheduledSmallCell top cs (e i))
    rw [he]
    change Fin.append (fun i => cell (cells.get i)) (fun i => cell (cells.get i)) i =
      cell (Fin.append cells.get cells.get i)
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  · change Fin.append (fun _ : Fin b => bulk) (fun _ : Fin b => bulk) i = bulk
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]

theorem scheduledRegularPrior_prime (cell : ℕ → Finset ℕ) (bulk P : Finset ℕ)
    (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    scheduledRegularPrior (fun j => primeSubsetPrior P (cell j))
      (primeSubsetPrior P bulk) top cs n m =
      fun i => primeSubsetPrior P (scheduledRegularPrimeSets cell bulk top cs n m i) := by
  funext i
  rcases i with ⟨j, i | i⟩ <;> rfl

end Ostmann

end OAI

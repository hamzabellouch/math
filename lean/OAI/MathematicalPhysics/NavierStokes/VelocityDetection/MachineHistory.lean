import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TapeCodes
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.StacksOptionStep
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Prelude

namespace OAI

noncomputable section
namespace VelocityDetection.MachineHistory
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Turing Stacks
variable {b N : ℕ} [NeZero b] [NeZero N]

def table (M : TM0.Machine (Fin b) (Fin N)) :
    Fin (N + 1) → Fin b → Option (Rule (Fin (N + 1)) b) :=
  Prelude.table' (TapeCodes.table M) 0

def initial (w : List (Fin b)) : Stacks.Configuration (Fin (N + 1)) :=
  Prelude.initial 0 (TapeCodes.word w)

def initialExponent (w : List (Fin b)) : ℕ := w.length + 1

@[simp] theorem exponent_pos {b : ℕ} [NeZero b] (w : List (Fin b)) :
    1 ≤ initialExponent w := by
  simp [initialExponent]

theorem initial_fits (hb : 0 < b) (w : List (Fin b)) :
    (initial (N := N) w).leftStack < capacity b (initialExponent w) 0 ∧
      (initial (N := N) w).rightStack < capacity b (initialExponent w) 0 :=
  TapeCodes.initial_fits (N := N) hb w

theorem initial_active (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    (lookup (NeZero.pos b) (table M) (initial w)).isSome :=
  Prelude.lookup_initial (NeZero.pos b) (TapeCodes.table M) 0 0 (TapeCodes.word w)

theorem halts_iff (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    History.Halts (NeZero.pos b) (table M) (initial w) ↔ (TM0.eval M w).Dom := by
  rw [table, initial, Prelude.halts_initial]
  exact (Stacks.eval_dom_iff_halts (NeZero.pos b) (TapeCodes.table M)
    (TapeCodes.initial w)).symm.trans (TapeCodes.eval_dom_iff M w)

theorem history_halts_iff (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)) :
    (∃ n, lookup (NeZero.pos b) (table M)
      (History.orbit (NeZero.pos b) (table M) ⟨initial w, 0⟩ n).tape = none) ↔
        (TM0.eval M w).Dom :=
  (History.halts_iff (NeZero.pos b) (table M) ⟨initial w, 0⟩).trans (halts_iff M w)

theorem history_fits (hb : 0 < b) (M : TM0.Machine (Fin b) (Fin N))
    (w : List (Fin b)) (n : ℕ) :
    History.Fits (capacity b (initialExponent w) n) (History.radix (N + 1) b ^ n)
      (History.orbit (NeZero.pos b) (table M) ⟨initial w, 0⟩ n) :=
  History.orbit_fits (NeZero.pos b) (table M) (exponent_pos w) _ (initial_fits hb w) n

end VelocityDetection.MachineHistory
end

end OAI

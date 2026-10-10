import OAI.Analysis.PeriodicLattice.Tape

namespace OAI

/-! Compilation of finite machines into planar velocity data. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingCompiler {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace CompilerPlanar

open Scales StackCode RuleTable Planar
open scoped ContDiff

def radix (d : Input) : ℕ := max 2 (max d.machine.states d.machine.symbols)

theorem radix_ge_two (d : Input) : 2 ≤ radix d := le_max_left _ _
theorem states_le_radix (d : Input) : d.machine.states ≤ radix d :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem symbols_le_radix (d : Input) : d.machine.symbols ≤ radix d :=
  (le_max_right _ _).trans (le_max_right _ _)

def loadingCode (d : Input) : ℕ := configurationCode (radix d) d 0

def nextTable (d : Input) := RuleTable.next (radix d) d.word.length d.machine
def haltTable (d : Input) := RuleTable.halt (radix d) d.word.length d.machine

def velocity (d : Input) : ℝ → Point → Point :=
  ruleField (radix d) d.word.length (loadingCode d) (nextTable d) (haltTable d)

def path (d : Input) : ℝ → Point :=
  curve (radix d) d.word.length (codes (nextTable d) (loadingCode d)) (haltTable d)

theorem loadingCode_bound (d : Input) (hd : d.WellFormed) :
    loadingCode d < capacity (radix d) d.word.length 0 :=
  configurationCode_bound (radix_ge_two d) d hd (symbols_le_radix d) (states_le_radix d) 0

theorem nextTable_bound (d : Input) (hd : d.WellFormed) (n : ℕ) (j : ℤ) :
    nextTable d n j < capacity (radix d) d.word.length (n + 1) :=
  next_bound (radix_ge_two d) _ _ hd.1 (symbols_le_radix d) (states_le_radix d) n j

theorem nextTable_periodic (d : Input) (n : ℕ) :
    Function.Periodic (nextTable d n) (capacity (radix d) d.word.length n : ℤ) :=
  next_periodic _ _ _ _

theorem haltTable_periodic (d : Input) (n : ℕ) :
    Function.Periodic (haltTable d n) (capacity (radix d) d.word.length n : ℤ) :=
  halt_periodic _ _ _ _

theorem velocity_contDiff (d : Input) : ContDiff ℝ ∞ (fun tx : ℝ × Point => velocity d tx.1 tx.2) :=
  field_contDiff _ _ _ _ _

theorem velocity_start (d : Input) (x : Point) : velocity d 0 x = 0 := field_at_start _ _ _ _ _ x

theorem velocity_periodic (d : Input) (t x : ℝ) : Function.Periodic (fun y => velocity d t (x, y)) 1 := by
  apply field_periodic_y (radix_ge_two d)
  · intro n j
    simp only [nextTable_periodic d n j]
  · intro n j
    simp only [haltTable_periodic d n j]

theorem path_contDiff (d : Input) : ContDiff ℝ ∞ (path d) := curve_contDiff _ _ _ _

theorem path_start (d : Input) : path d 0 = (1 / 4, 1 / 2) := curve_start _ _ _ _

theorem path_solves (d : Input) (hd : d.WellFormed) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (path d) (velocity d t (path d t)) t :=
  curve_solves (radix_ge_two d) _ _ _ _ (loadingCode_bound d hd)
    (nextTable_bound d hd) (nextTable_periodic d) (haltTable_periodic d) ht

theorem path_unique (d : Input) (hd : d.WellFormed) {Y : ℝ → Point}
    (hY₀ : Y 0 = (1 / 4, 1 / 2))
    (hY : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt Y (velocity d t (Y t)) (Set.Ici 0) t)
    {t : ℝ} (ht : 0 ≤ t) : Y t = path d t :=
  curve_unique (radix_ge_two d) _ _ _ _ (loadingCode_bound d hd)
    (nextTable_bound d hd) (nextTable_periodic d) (haltTable_periodic d) hY₀ hY ht

theorem path_event_iff (d : Input) (hd : d.WellFormed) :
    MaterialEvent (fun t => embed (path d t)) ↔ Halts d := by
  rw [path, curve_event_iff (radix_ge_two d)]
  unfold loadingCode
  rw [codes_flag_iff (nextTable d) (haltTable d) (configurationCode (radix d) d)
    (next_code (radix_ge_two d) d hd (symbols_le_radix d) (states_le_radix d))]
  unfold Halts haltTable
  simp only [halt_code (radix_ge_two d) d hd (symbols_le_radix d) (states_le_radix d), Option.isNone_iff_eq_none]

end CompilerPlanar

end
end PeriodicLattice

end OAI

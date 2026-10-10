import OAI.Combinatorics.HoneycombCorridor.Polygons

namespace OAI

namespace PolynomialVacuumBridge.Corridor

def heading (g : Germ) : ZMod 6 :=
  2 * (g.2.val : ZMod 6) + match g.1 with
    | .up _ _ => 0
    | .down _ _ => 3

@[simp] theorem heading_advance (g : Germ) (b : Bool) :
    heading (advance g b) = heading g + (turnUnit b : ZMod 6) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [heading, advance, outgoingSlot, neighbor, turnUnit] <;> decide

theorem heading_terminal (g : Germ) (w : List Bool) :
    heading (terminalGerm g w) = heading g + (turnUnits w : ZMod 6) := by
  induction w generalizing g with
  | nil => simp [terminalGerm,turnUnits]
  | cons b w ih =>
      simp only [terminalGerm, ih, heading_advance, turnUnits, List.map_cons,
        List.sum_cons, Int.cast_add]
      ring

 

theorem closed_turns_divisible_six (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) : (6 : ℤ) ∣ turnUnits w := by
  have h := heading_terminal g w
  rw [hc] at h
  have hz : (turnUnits w : ZMod 6) = 0 := by simpa using h.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz

end PolynomialVacuumBridge.Corridor

end OAI

import OAI.Combinatorics.HoneycombChords.Geometry

namespace OAI

/-! Strict honeycomb bridges from a fixed bottom port, with critical mass summed
over compatible top ports. The height-zero mass has the renewal normalization one.

The convention follows the finite inputs in *Critical honeycomb chords with
prescribed boundary endpoints*. -/

namespace CriticalHoneycomb
open scoped ENNReal

def strip (h : ℕ) : Set Center := {v | 0 ≤ v.2.1 ∧ v.2.1 < (h : ℤ)}
def StrictBridge (h : ℕ) :=
  {p : List Center // IsTrace (strip h) p ∧ p.head? = some (up 0 0) ∧
    ∃ i : ℤ, p.getLast? = some (down i ((h : ℤ) - 1))}
noncomputable def bridgeMass (h : ℕ) : ℝ≥0∞ :=
  if h = 0 then 1 else ∑' p : StrictBridge h, weight p.val


end CriticalHoneycomb

end OAI

import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace WeakPinned
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def distanceFiber (P : Finset Plane) (x y : Plane) : Finset Plane :=
  (P.erase x).filter (fun z => dist z x = dist y x)

def k (P : Finset Plane) (x y : Plane) : ℕ :=
  (distanceFiber P x y).card

def richPairs (P : Finset Plane) (s : ℝ) : Finset (Plane × Plane) :=
  (P ×ˢ P).filter (fun xy => xy.1 ≠ xy.2 ∧
    (P.card : ℝ) ^ s ≤ (k P xy.1 xy.2 : ℝ))

def pairFraction (P : Finset Plane) (s : ℝ) : ℝ :=
  (richPairs P s).card / ((P.card : ℝ) * ((P.card : ℝ) - 1))

def F (n : ℕ) (s : ℝ) : ℝ :=
  if 2 ≤ n then sSup {a : ℝ | ∃ P : Finset Plane, P.card = n ∧ a = pairFraction P s}
  else 0

def distances (P : Finset Plane) (x : Plane) : Finset ℝ :=
  (P.erase x).image (fun y => dist y x)

def badPins (P : Finset Plane) (ε : ℝ) : Finset Plane :=
  P.filter (fun x => ((distances P x).card : ℝ) < (P.card : ℝ) ^ (1 - ε))

def badPinFraction (P : Finset Plane) (ε : ℝ) : ℝ :=
  (badPins P ε).card / (P.card : ℝ)

def B (n : ℕ) (ε : ℝ) : ℝ :=
  if 0 < n then sSup {a : ℝ | ∃ P : Finset Plane, P.card = n ∧ a = badPinFraction P ε}
  else 0

/- Uniform multiplicity and pinned-distance convergence statements. -/
def MainStatement : Prop :=
  ∀ s : ℝ, 0 < s → Tendsto (fun n : ℕ => F n s) atTop (nhds 0)

def PinsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => B n ε) atTop (nhds 0)

end WeakPinned

end

end OAI

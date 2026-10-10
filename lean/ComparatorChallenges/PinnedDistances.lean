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

theorem main (s : ℝ) (hs : 0<s) : Tendsto (fun n : ℕ => F n s) atTop (𝓝 0) := by
  sorry

end WeakPinned

end

end OAI

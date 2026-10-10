import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

namespace OAI

/-! A finite, kernel-checked classification of simple two-regular graphs on
five vertices.  Ten Boolean edge choices are checked, not matrices over a
restricted alphabet. -/

namespace MUB6

def fiveGraph (b : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool :=
  !![false, b 0, b 1, b 2, b 3;
     b 0, false, b 4, b 5, b 6;
     b 1, b 4, false, b 7, b 8;
     b 2, b 5, b 7, false, b 9;
     b 3, b 6, b 8, b 9, false]

def twoRegularFive (b : Fin 10 → Bool) : Prop :=
  ∀ i, (Finset.univ.filter (fun j => fiveGraph b i j = true)).card = 2

def fiveCycleOrder : Fin 12 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![0, 1, 2, 4, 3], ![0, 1, 3, 2, 4], ![0, 1, 3, 4, 2],
    ![0, 1, 4, 2, 3], ![0, 1, 4, 3, 2], ![0, 2, 1, 3, 4], ![0, 2, 1, 4, 3],
    ![0, 2, 3, 1, 4], ![0, 2, 4, 1, 3], ![0, 3, 1, 2, 4], ![0, 3, 2, 1, 4]]

def canonicalFiveCycle : Fin 5 → Fin 5 → Bool :=
  fiveGraph ![true, false, false, true, true, false, false, true, false, true]

theorem fiveCycleOrder_bijective : ∀ c, Function.Bijective (fiveCycleOrder c) := by
  decide +kernel

theorem twoRegularFive_is_cycle : ∀ b, twoRegularFive b →
    ∃ c, ∀ i j, fiveGraph b (fiveCycleOrder c i) (fiveCycleOrder c j) =
      canonicalFiveCycle i j := by
  unfold twoRegularFive
  decide +kernel

noncomputable def fiveCyclePermutation (c : Fin 12) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (fiveCycleOrder c) (fiveCycleOrder_bijective c)

end MUB6

end OAI

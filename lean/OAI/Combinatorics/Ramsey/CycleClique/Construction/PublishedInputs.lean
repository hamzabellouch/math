import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OAI

/-!
# The published Hamiltonicity input

Chvátal and Erdős, *A note on Hamiltonian circuits*, Discrete Mathematics
2 (1972), 111–113, Theorem 1:
<https://users.renyi.hu/~p_erdos/1972-02.pdf>.

Only its `s = 2` specialization at order at least six is needed here.
The proposition below is an explicit parameter of the conditional
development, not an axiom or an assumed instance.
-/

namespace CycleClique.Construction
/-- The precise Chvátal–Erdős specialization used in the size test.
Connectivity after every one-vertex deletion is the required
two-connectivity condition at this order. -/
def CEAlphaTwo : Prop :=
  ∀ (V : Type) [Fintype V] (H : SimpleGraph V),
    6 ≤ Fintype.card V → H.Connected →
    (∀ v : V, (H.induce {w | w ≠ v}).Connected) →
    ¬ HasIndependent H 3 → HasCycle H (Fintype.card V)

end CycleClique.Construction

end OAI

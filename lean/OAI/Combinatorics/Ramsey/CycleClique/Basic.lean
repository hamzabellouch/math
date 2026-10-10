import Mathlib

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ

noncomputable def cycleCliqueRamsey (m n : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyProperty m n N}

 
def MainTarget : Prop :=
  ∀ m n : ℕ, n ≤ m → 3 ≤ n → (m, n) ≠ (3, 3) →
    cycleCliqueRamsey m n = (m - 1) * (n - 1) + 1

 
def ExceptionalTarget : Prop := cycleCliqueRamsey 3 3 = 6

 
def closedNeighborhood {V : Type*} (G : SimpleGraph V) (I : Set V) : Set V :=
  I ∪ {v | ∃ u ∈ I, G.Adj u v}

 
def ColouredPathTarget : Prop :=
  ∀ (V : Type) [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : ℕ), 4 ≤ s → H.Connected → ¬ H.IsBipartite →
    ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H → (∀ v, s ≤ H.degree v) →
    (∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard) →
    ∀ (χ : V → Fin 2), (∃ y z, χ y ≠ χ z) →
      ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * s - 2 →
        ∃ y z, χ y ≠ χ z ∧ ∃ p : H.Walk y z, p.IsPath ∧ p.length = ℓ

end CycleClique

end OAI

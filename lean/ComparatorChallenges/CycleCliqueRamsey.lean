import Mathlib

namespace OAI

 

namespace CycleClique
open scoped SimpleGraph

 

def RamseyProperty (m n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ

 

noncomputable def cycleCliqueRamsey (m n : ℕ) : ℕ :=
  sInf {N : ℕ | RamseyProperty m n N}

 

theorem thm_main :
    (∀ m n : ℤ, n ≤ m → 3 ≤ n → (m, n) ≠ (3, 3) →
      (cycleCliqueRamsey m.toNat n.toNat : ℤ) = (m - 1) * (n - 1) + 1) ∧
    cycleCliqueRamsey 3 3 = 6 := by
  sorry

end CycleClique

end OAI

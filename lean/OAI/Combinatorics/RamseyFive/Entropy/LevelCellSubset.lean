import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BlockReveal

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]
lemma levelCell_subset_support (p : Law α) (n : Level p) : levelCell p n⊆support p := by
  intro a ha
  exact (mem_support p a).mpr ((mem_levelCell p n a).mp ha).1
lemma levelCell_cap (p : Law α) (N : ℝ) (hN : ((support p).card:ℝ) ≤ N) (n : Level p) :
    ((levelCell p n).card:ℝ) ≤ N :=
  (show ((levelCell p n).card:ℝ) ≤ (support p).card by
    exact_mod_cast Finset.card_le_card (levelCell_subset_support p n)).trans hN
end SharpRamseyFive.FiniteEntropy

end OAI

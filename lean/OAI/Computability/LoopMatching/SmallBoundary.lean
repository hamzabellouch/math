import OAI.Computability.LoopMatching.Model

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

def emptyPartialMatching (n : ℕ) : PartialMatching n :=
  ⟨∅, by
    intro v e he
    simp at he⟩

@[simp] theorem loopVertices_emptyPartialMatching (n : ℕ) :
    loopVertices (emptyPartialMatching n) = Finset.univ := by
  classical
  ext v
  simp [loopVertices, emptyPartialMatching]

theorem partialMatching_eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1)
    (M : PartialMatching n) : M = emptyPartialMatching n := by
  apply Subtype.ext
  ext e
  have hleft := e.val.1.isLt
  have hright := e.val.2.isLt
  have horder := e.property
  change e.val.1.val < e.val.2.val at horder
  omega

theorem count_eq_loop_product_of_le_one (G : Input) (hn : G.n ≤ 1) :
    count G = ∏ v : Fin G.n, loopMultiplicity G v := by
  classical
  unfold count
  rw [Finset.sum_eq_single (emptyPartialMatching G.n)]
  · simp [weight, emptyPartialMatching, loopVertices]
  · intro M _ hne
    exact (hne (partialMatching_eq_empty_of_le_one hn M)).elim
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem count_order_zero (G : Input) (hn : G.n = 0) : count G = 1 := by
  rw [count_eq_loop_product_of_le_one G (by omega)]
  apply Finset.prod_eq_one
  intro v _
  have hv := v.isLt
  omega

theorem count_order_one (G : Input) (hn : G.n = 1) :
    count G = loopMultiplicity G ⟨0, by omega⟩ := by
  classical
  rw [count_eq_loop_product_of_le_one G (by omega)]
  apply Finset.prod_eq_single (⟨0, by omega⟩ : Fin G.n)
  · intro v _ hne
    have hv := v.isLt
    have heq : v = (⟨0, by omega⟩ : Fin G.n) := by
      apply Fin.ext
      change v.val = 0
      omega
    exact (hne heq).elim
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

end LoopMatching

end

end OAI

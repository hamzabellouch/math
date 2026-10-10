import OAI.Combinatorics.ContingencyTables.Counting.CompanionFactorialApplication

namespace OAI

/-! # The expanded physical forest box still has a short cardinality bound

The tree interval width 20db has at most (b+1)^2 integer positions
when every large capacity is at least 20d. This provides a uniform bound
for the positive equality-softened balanced sums before taking limits.
-/

namespace ContingencyTables.ForestBoxCardinality

open scoped BigOperators Classical
open CompanionFactorialApplication ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

lemma width_add_one_le_square (A : Instance I J) (hW : 20*A.d ≤ A.W) (i : I) (j : J) :
    width A.T A.d A.b i j+1 ≤ (A.b i j+1)^2 := by
  unfold width
  split_ifs with ht
  · have hs : A.small i j=false := A.hTG ht
    have hb : 20*A.d ≤ A.b i j := hW.trans (A.hlarge i j hs).1
    nlinarith
  · nlinarith

abbrev Assignments (A : Instance I J) :=
  (a : I×J) → Fin (width A.T A.d A.b a.1 a.2+1)

theorem cardinality_le_square (A : Instance I J) (hW : 20*A.d ≤ A.W) :
    Fintype.card (Assignments A) ≤ (∏ a : I×J,(A.b a.1 a.2+1))^2 := by
  simp only [Assignments,Fintype.card_pi,Fintype.card_fin]
  calc
    _ ≤ ∏ a : I×J,(A.b a.1 a.2+1)^2 := by
      apply Finset.prod_le_prod
      intro a _
      exact width_add_one_le_square A hW a.1 a.2
    _ = _ := Finset.prod_pow Finset.univ 2 (fun a : I×J => A.b a.1 a.2+1)

/-- The full balanced physical box, including every expanded tree
interval, has at most 2^K profiles under the source's bit-size allowance. -/
theorem cardinality_le_two_pow (A : Instance I J) (hW : 20*A.d ≤ A.W)
    (L K : ℕ) (hL : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^L) (hK : 2*L ≤ K) :
    Fintype.card (Assignments A) ≤ 2^K := by
  calc
    _ ≤ (∏ a : I×J,(A.b a.1 a.2+1))^2 := cardinality_le_square A hW
    _ ≤ (2^L)^2 := Nat.pow_le_pow_left hL 2
    _ = 2^(2*L) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hK

end ContingencyTables.ForestBoxCardinality

end OAI

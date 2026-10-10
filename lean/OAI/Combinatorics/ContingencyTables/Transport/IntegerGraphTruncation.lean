import OAI.Combinatorics.ContingencyTables.Transport.IntegerTruncatedTransport

namespace OAI

/-! # The zero-extended energy is the actual box-restricted graph energy -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open IntegerBoxTruncation BalancedBox

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem graphEnergy_truncate (V : Finset (C → ℕ)) (f H : (C → ℕ) → ℝ)
    (m : C → ℕ) (R : ℕ) (hf : ∀ x, 0 ≤ f x) :
    integerGraphEnergy V (truncate f m R) H=
      integerGraphEnergy (V.filter (fun x => InBox m x ∧ (∑ i, x i)=R)) f H := by
  unfold integerGraphEnergy
  rw [←Finset.filter_product,Finset.filter_filter]
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : IntegerExchangeAdjacent e.1 e.2
  · by_cases hx : InBox m e.1 ∧ (∑ i, e.1 i)=R
    · by_cases hy : InBox m e.2 ∧ (∑ i, e.2 i)=R
      · simp only [ha,hx,hy,↓reduceIte,and_self,edgeTerm,truncate]
      · simp [ha,hx,hy,edgeTerm,truncate,min_eq_right (hf e.1)]
    · by_cases hy : InBox m e.2 ∧ (∑ i, e.2 i)=R
      · simp [ha,hx,hy,edgeTerm,truncate,min_eq_left (hf e.2)]
      · simp [ha,hx,hy,edgeTerm,truncate]
  · simp only [ha,and_false,↓reduceIte]

end ContingencyTables.IntegerWeightedTransport

end OAI

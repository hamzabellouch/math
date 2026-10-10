import OAI.Combinatorics.ContingencyTables.Transport.FiniteExchangeDegree

namespace OAI

/-! # Arithmetic recognition of unit-exchange edges -/

namespace ContingencyTables.IntegerWeightedTransport
open FactorialSignatures

variable {C : Type*} [DecidableEq C]

lemma exchangeTarget_adjacent (X : C → ℕ) (i j : C)
    (hij : i≠j) (hj : 0<X j) :
    IntegerExchangeAdjacent X (exchangeTarget X i j) := by
  let D : C → ℕ := fun a => X a+if a=i then 1 else 0
  refine ⟨D,i,j,hij,?_,?_,?_,?_⟩
  · simp only [D,ite_true]
    omega
  · simpa only [D,Ne.symm hij,ite_false,Nat.add_zero] using hj
  · funext a
    simp only [D,removeOne]
    split_ifs <;> omega
  · rfl

/-- The test quantifies only over two coordinates, never over profiles. -/
theorem adjacent_iff_arithmetic (X Y : C → ℕ) :
    IntegerExchangeAdjacent X Y ↔
      ∃ i j,i≠j ∧ 0<X j ∧ Y=exchangeTarget X i j := by
  constructor
  · rintro ⟨D,i,j,hij,hi,hj,rfl,rfl⟩
    refine ⟨i,j,hij,?_,?_⟩
    · simpa only [removeOne,Ne.symm hij,ite_false,Nat.sub_zero] using hj
    · funext a
      unfold exchangeTarget removeOne
      by_cases hai : a=i
      · subst a
        simp only [hij,ite_true,ite_false,Nat.sub_zero]
        omega
      · by_cases haj : a=j
        · subst a
          simp only [hai,ite_true,ite_false,Nat.sub_zero,Nat.add_zero]
        · simp only [hai,haj,ite_false,Nat.sub_zero,Nat.add_zero]
  · rintro ⟨i,j,hij,hj,rfl⟩
    exact exchangeTarget_adjacent X i j hij hj

end ContingencyTables.IntegerWeightedTransport

end OAI

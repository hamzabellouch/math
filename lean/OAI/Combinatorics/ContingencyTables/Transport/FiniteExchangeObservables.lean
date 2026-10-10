import OAI.Combinatorics.ContingencyTables.Transport.FiniteExchangeDegree

namespace OAI

/-! # Unit exchanges change each selected coordinate sum by at most two -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical
open FactorialSignatures

variable {C : Type*} [Fintype C] [DecidableEq C]

noncomputable def linearObservable (a : C → ℤ) (z : C → ℕ) : ℤ := ∑ k,a k*(z k:ℤ)

lemma linearObservable_removeOne (a : C → ℤ) (D : C → ℕ) (i : C) (hi : 0 < D i) :
    linearObservable a (removeOne D i)=linearObservable a D-a i := by
  have ht (k : C) : (removeOne D i k:ℤ)=(D k:ℤ)-(if k=i then 1 else 0) := by
    by_cases hk : k=i
    · subst k
      simp only [removeOne,ite_true]
      omega
    · simp only [removeOne,hk,ite_false,Nat.sub_zero,sub_zero]
  unfold linearObservable
  simp_rw [ht,mul_sub]
  rw [Finset.sum_sub_distrib]
  simp

lemma exchange_observable_difference (a : C → ℤ) (X Y : C → ℕ)
    (hxy : IntegerExchangeAdjacent X Y) :
    ∃ i j,linearObservable a Y-linearObservable a X=a i-a j := by
  obtain ⟨D,i,j,_,hi,hj,rfl,rfl⟩ := hxy
  refine ⟨i,j,?_⟩
  rw [linearObservable_removeOne a D i hi,linearObservable_removeOne a D j hj]
  ring

theorem exchange_observable_abs_le_two (a : C → ℤ) (ha : ∀ i,|a i| ≤ 1)
    (X Y : C → ℕ) (hxy : IntegerExchangeAdjacent X Y) :
    |linearObservable a Y-linearObservable a X| ≤ 2 := by
  obtain ⟨i,j,he⟩ := exchange_observable_difference a X Y hxy
  rw [he]
  exact (abs_sub _ _).trans (by linarith [ha i,ha j])

theorem exchange_selected_sum_abs_le_two (p : C → Prop) (X Y : C → ℕ)
    (hxy : IntegerExchangeAdjacent X Y) :
    |((∑ k,if p k then Y k else 0:ℕ):ℤ)-((∑ k,if p k then X k else 0:ℕ):ℤ)| ≤ 2 := by
  have ha : ∀ k,|(if p k then 1 else 0:ℤ)| ≤ 1 := by
    intro k
    split_ifs <;> norm_num
  have h := exchange_observable_abs_le_two (fun k => if p k then 1 else 0) ha X Y hxy
  simpa only [linearObservable,ite_mul,one_mul,zero_mul,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] using h

end ContingencyTables.IntegerWeightedTransport

end OAI

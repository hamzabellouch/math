import OAI.Combinatorics.PolynomialVacuum.Algebra.FullCyclicity

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def natCharge (N : ℕ) (s : ℕ → Spin) : ℤ := ∑ j ∈ Finset.range N, charge (s j)

theorem natCharge_removePair (n i : ℕ) (hi : i≤n) (s : ℕ → Spin) :
    natCharge (n+2) s=charge (s i)+charge (s (i+1))+natCharge n (skipTwo i s) := by
  have hn : n=i+(n-i) := by omega
  have hN : n+2=(i+2)+(n-i) := by omega
  have hr : ∑ j ∈ Finset.range i, charge (skipTwo i s j)=∑ j ∈ Finset.range i, charge (s j) := by
    apply Finset.sum_congr rfl
    intro j hj; simp [skipTwo,Finset.mem_range.mp hj]
  have ht : ∑ j ∈ Finset.range (n-i), charge (skipTwo i s (i+j))=
      ∑ j ∈ Finset.range (n-i), charge (s (i+2+j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjj : ¬ i + j < i := by omega
    simp only [skipTwo,ite_eq_right hjj]
    congr 2
    omega
  unfold natCharge
  conv_lhs => rw [hN,Finset.sum_range_add,Finset.sum_range_succ,Finset.sum_range_succ]
  conv_rhs => arg 2; rw [hn,Finset.sum_range_add]
  rw [hr,ht]
  ring

theorem skipTwo_replacePair (i : ℕ) (s : ℕ → Spin) (ab : Pair) :
    skipTwo i (replacePair s i (i+1) ab)=skipTwo i s := by
  funext k
  unfold skipTwo
  split_ifs with h
  · exact replacePair_other s (by omega) (by omega) ab
  · exact replacePair_other s (by omega) (by omega) ab

theorem natCharge_replacePair {N i : ℕ} (hi : i+1<N) (s : ℕ → Spin) (ab : Pair) :
    natCharge N (replacePair s i (i+1) ab)=
      natCharge N s-charge (s i)-charge (s (i+1))+charge ab.1+charge ab.2 := by
  have hn : N=(N-2)+2 := by omega
  rw [hn,natCharge_removePair (N-2) i (by omega),natCharge_removePair (N-2) i (by omega)]
  rw [replacePair_left s (by omega),replacePair_right,skipTwo_replacePair]
  ring

theorem exchange_charge_conservation (x y : ℂ) (a b : Pair)
    (hab : charge a.1+charge a.2≠charge b.1+charge b.2) :
    exchangeNumerator x y a b=0 := by
  rcases a with ⟨a,c⟩
  rcases b with ⟨b,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [charge,exchangeNumerator_eq_table,exchangeTable]

end PolynomialVacuumAlgebra

end OAI

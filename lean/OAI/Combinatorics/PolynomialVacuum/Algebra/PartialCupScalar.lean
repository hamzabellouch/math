import OAI.Combinatorics.PolynomialVacuum.Algebra.TrainEvaluation

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem pullSite_before {α : Type*} {j k : ℕ} (h : j < k) (m : ℕ) (c : α) (X : ℕ → α) :
    pullSite k m c X j=X j := by simp [pullSite,insertOne,skipOne,h,show j < k+m by omega]

theorem skipTwo_pullSite {α : Type*} (i m : ℕ) (c : α) (X : ℕ → α) :
    skipTwo i (pullSite (i+1) m c X)=skipOne i (skipOne (i+1+m) X) := by
  funext j
  simp only [skipTwo,pullSite,insertOne,skipOne]
  split_ifs <;> congr 1 <;> omega

theorem prod_skipOne_penultimate {α β : Type*} [CommMonoid β] (f : α → β)
    (X : ℕ → α) {n i : ℕ} (hi : i < n) :
    (∏ j ∈ Finset.range n, f (skipOne i (skipOne n X) j))=
      (∏ j ∈ Finset.range i, f (X j))*
      (∏ j ∈ Finset.range (n-i-1), f (X (i+1+j)))*f (X (n+1)) := by
  have hn : n=(n-1)+1 := by omega
  nth_rw 1 [hn]
  rw [Finset.prod_range_succ]
  have hl : skipOne i (skipOne n X) (n-1)=X (n+1) := by
    simp [skipOne,show ¬n-1 < i by omega,show n-1+1=n by omega]
  rw [hl]
  congr 1
  have hn' : n-1=i+(n-i-1) := by omega
  rw [hn',Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp [skipOne,hj',show j < n by omega]
  · apply Finset.prod_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp [skipOne,show ¬i+j < i by omega,show i+1+j < n by omega,
      show i+j+1=i+1+j by omega]

theorem naturalFusion_pull_penultimate (n i : ℕ) (hi : i < n) (X : ℕ → ℂ) :
    naturalFusion n i (pullSite (i+1) (n-i-1) (T*X i) X)=
      ((1+T)*X i*leftFusion i X*fusionPair (X i) (X (n+1)))*
        trainDenominator (T*X i) X (i+1) (n-i-1) := by
  simp only [naturalFusion,pullSite_before (by omega : i < i+1),fusionProduct,
    skipTwo_pullSite,show i+1+(n-i-1)=n by omega]
  rw [prod_skipOne_penultimate _ X hi]
  simp only [leftFusion,trainDenominator_prod,← fusionPair_denominator]
  ring

end PolynomialVacuumAlgebra

end OAI

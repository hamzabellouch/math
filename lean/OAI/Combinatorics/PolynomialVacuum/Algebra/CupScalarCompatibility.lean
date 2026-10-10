import OAI.Combinatorics.PolynomialVacuum.Algebra.CupTransport
import OAI.Combinatorics.PolynomialVacuum.Algebra.FusionScalars

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

@[simp] theorem skipTwo_zero_apply {α : Type*} (X : ℕ → α) (k : ℕ) :
    skipTwo 0 X k=X (k+2) := by simp [skipTwo]

theorem skipTwo_skipOne_after {α : Type*} (j : ℕ) (X : ℕ → α) :
    skipTwo 0 (skipOne (j+2) X)=skipOne j (skipTwo 0 X) := by
  funext k
  simp only [skipTwo_zero_apply,skipOne]
  split_ifs <;> congr 1 <;> omega

theorem skipTwo_insertOne_after {α : Type*} (j : ℕ) (c : α) (X : ℕ → α) :
    skipTwo 0 (insertOne (j+2) c X)=insertOne j c (skipTwo 0 X) := by
  funext k
  simp only [skipTwo_zero_apply,insertOne]
  split_ifs <;> congr 1 <;> omega

theorem fusionProduct_insertLast (a c : ℂ) (X : ℕ → ℂ) (m : ℕ) :
    fusionProduct a (insertOne m c X) (m+1)=fusionProduct a X m*fusionPair a c := by
  simp only [fusionProduct,Finset.prod_range_succ,insertOne_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [insertOne,ite_eq_left (Finset.mem_range.mp hk)]

theorem leftFusion_dropTwo (j : ℕ) (X : ℕ → ℂ) :
    leftFusion (j+2) X=fusionPair (X (j+2)) (X 0)*fusionPair (X (j+2)) (X 1)*
      leftFusion j (skipTwo 0 X) := by
  simp only [leftFusion,skipTwo_zero_apply]
  rw [show j+2=2+j by omega,Finset.prod_range_add]
  simp only [Finset.prod_range_succ,Finset.range_zero,Finset.prod_empty,one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Nat.add_comm 2 k]

 

theorem firstCup_scalar_compatibility (m j : ℕ) (hj : j ≤ m) (X : ℕ → ℂ)
    (hX : X 1=T*X 0) :
    ((1+T)*X (j+2)*leftFusion (j+2) X)*naturalFusion m 0 (skipOne (j+2) X)=
    naturalFusion (m+2) 0 (insertOne (m+3) (T*X (j+2)) X)*
      ((1+T)*skipTwo 0 X j*leftFusion j (skipTwo 0 X)) := by
  have hx : skipOne (j+2) X 0=X 0 := by simp [skipOne]
  have hy : insertOne (m+3) (T*X (j+2)) X 0=X 0 := by simp [insertOne]
  have hs := fusionProduct_skipOne (X 0) (skipTwo 0 X) m j hj
  have hf := fusionPair_four_point (X 0) (X (j+2))
  simp only [skipTwo_zero_apply] at hs
  simp only [naturalFusion,hx,hy,skipTwo_skipOne_after,leftFusion_dropTwo,hX,
    show m+3=(m+1)+2 by omega,skipTwo_insertOne_after,fusionProduct_insertLast,
    skipTwo_zero_apply]
  rw [← hs]
  linear_combination (1+T)^2 * X 0 * X (j+2) * leftFusion j (skipTwo 0 X) *
    fusionProduct (X 0) (skipOne j (skipTwo 0 X)) m * hf

end PolynomialVacuumAlgebra

end OAI

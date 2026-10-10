import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCandidateEndpoints
import OAI.Combinatorics.PolynomialVacuum.Algebra.CupPointwiseSlide

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 
def pullSite {α : Type*} (k m : ℕ) (c : α) (X : ℕ → α) : ℕ → α :=
  insertOne k c (skipOne (k+m) X)

theorem pullSite_zero {α : Type*} (k : ℕ) (c : α) (X : ℕ → α) :
    pullSite k 0 c X=Function.update X k c := by
  funext j
  simp only [pullSite,insertOne,skipOne,Nat.add_zero,Function.update_apply]
  split_ifs <;> congr 1 <;> omega

@[simp] theorem pullSite_at {α : Type*} (k m : ℕ) (c : α) (X : ℕ → α) :
    pullSite k m c X k=c := by simp [pullSite,insertOne]

@[simp] theorem pullSite_next {α : Type*} (k m : ℕ) (c : α) (X : ℕ → α) :
    pullSite k (m+1) c X (k+1)=X k := by simp [pullSite,insertOne,skipOne]

theorem swapSite_pullSite {α : Type*} (k m : ℕ) (c : α) (X : ℕ → α) :
    swapSite k (pullSite k (m+1) c X)=pullSite (k+1) m c X := by
  funext j
  by_cases h0 : j=k
  · subst j; simp [pullSite,insertOne,skipOne,show k < k+1+m by omega]
  by_cases h1 : j=k+1
  · subst j; simp
  rw [swapSite_other h0 h1]
  simp only [pullSite,insertOne,skipOne]
  split_ifs <;> congr 1 <;> omega

theorem trainDenominator_prod (c : ℂ) (X : ℕ → ℂ) (k m : ℕ) :
    trainDenominator c X k m=∏ j ∈ Finset.range m, exchangeDenominator c (X (k+j)) := by
  induction m generalizing k with
  | zero => simp [trainDenominator]
  | succ m ih =>
    rw [trainDenominator,ih,Finset.prod_range_succ']
    simp only [Nat.add_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [show k+(j+1)=k+1+j by omega]

 
theorem braidTrain_pull_exchange {Ψ : NatSpectralTensor} {n : ℕ}
    (hΨ : LowerExchange Ψ n) (k m : ℕ) (hkm : k+m < n) (c : ℂ) (X : ℕ → ℂ) :
    braidTrain c X k m (Ψ (pullSite k m c X))=
      trainDenominator c X k m • Ψ (Function.update X (k+m) c) := by
  induction m generalizing k with
  | zero => simp [braidTrain,trainDenominator,pullSite_zero]
  | succ m ih =>
    rw [braidTrain,Module.End.mul_apply]
    have he := hΨ k (by omega) (pullSite k (m+1) c X)
    simp only [pullSite_at,pullSite_next,swapSite_pullSite] at he
    rw [he,map_smul,ih (k+1) (by omega),smul_smul]
    simp only [trainDenominator]
    rw [mul_comm,show k+1+m=k+(m+1) by omega]

theorem braidTrain_snoc (c : ℂ) (X : ℕ → ℂ) (k m : ℕ) :
    braidTrain c X k (m+1)=siteR (k+m) c (X (k+m))*braidTrain c X k m := by
  induction m generalizing k with
  | zero => simp [braidTrain]
  | succ m ih =>
    rw [braidTrain,ih,mul_assoc,← braidTrain,
      show k+1+m=k+(m+1) by omega]

end PolynomialVacuumAlgebra

end OAI

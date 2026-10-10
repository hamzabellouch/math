import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCovariance

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

def insertOne {α : Type*} (i : ℕ) (a : α) (X : ℕ → α) : ℕ → α :=
 fun j => if j < i then X j else if j=i then a else X (j-1)

@[simp] theorem insertOne_self {α : Type*} (i : ℕ) (a : α) (X : ℕ → α) :
  insertOne i a X i=a := by simp [insertOne]
@[simp] theorem insertOne_next {α : Type*} (i : ℕ) (a : α) (X : ℕ → α) :
  insertOne i a X (i+1)=X i := by simp [insertOne]

theorem swapSite_insertOne {α : Type*} (i : ℕ) (a : α) (X : ℕ → α) :
  swapSite i (insertOne i a X)=insertOne (i+1) a X := by
 funext j
 simp only [swapSite,Function.comp_apply,Equiv.swap_apply_def,insertOne]
 split_ifs <;> congr 1 <;> omega

noncomputable def trainDenominator (c : ℂ) (X : ℕ → ℂ) (k : ℕ) : ℕ → ℂ
 | 0 => 1
 | m+1 => trainDenominator c X (k+1) m * exchangeDenominator c (X k)

 
theorem braidTrain_exchange {ψ : NatSpectralTensor} {n : ℕ}
  (hψ : LowerExchange ψ n) (c : ℂ) (X : ℕ → ℂ) (k m : ℕ) (hkm : k+m < n) :
  braidTrain c X k m (ψ (insertOne k c X))=
   trainDenominator c X k m • ψ (insertOne (k+m) c X) := by
 induction m generalizing k with
 | zero => simp [braidTrain,trainDenominator]
 | succ m ih =>
  have he := hψ k (by omega) (insertOne k c X)
  simp only [insertOne_self,insertOne_next,swapSite_insertOne] at he
  simp only [braidTrain,Module.End.mul_apply,he,map_smul,trainDenominator]
  rw [ih (k+1) (by omega),smul_smul]
  congr 1 <;> ring_nf

theorem braidTrain_cup_after (i k m : ℕ) (hik : i+2 ≤ k) (c : ℂ) (X : ℕ → ℂ) :
  braidTrain c X k m * cupLinear i =
   cupLinear i * braidTrain c (skipTwo i X) (k-2) m := by
 induction m generalizing k with
 | zero => simp [braidTrain]
 | succ m ih =>
  simp only [braidTrain,mul_assoc]
  rw [siteR_cup_after hik,← mul_assoc,ih (k+1) (by omega)]
  have hk : skipTwo i X (k-2)=X k := by
   simp [skipTwo,show ¬k-2 < i by omega,show k-2+2=k by omega]
  rw [show k+1-2=k-2+1 by omega,hk,mul_assoc]

theorem skipTwo_skipTwo {α : Type*} {i j : ℕ} (hij : i+2 ≤ j) (X : ℕ → α) :
  skipTwo (j-2) (skipTwo i X)=skipTwo i (skipTwo j X) := by
 funext k
 simp only [skipTwo]
 split_ifs <;> congr 1 <;> omega

theorem cupLinear_cup_after {i j : ℕ} (hij : i+2 ≤ j) :
  cupLinear j * cupLinear i = cupLinear i * cupLinear (j-2) := by
 ext W s
 simp only [Module.End.mul_apply,cupLinear,LinearMap.coe_mk,AddHom.coe_mk]
 have h0 : skipTwo j s i=s i := by simp [skipTwo,show i < j by omega]
 have h1 : skipTwo j s (i+1)=s (i+1) := by simp [skipTwo,show i+1 < j by omega]
 have h2 : skipTwo i s (j-2)=s j := by simp [skipTwo,show ¬j-2 < i by omega,show j-2+2=j by omega]
 have h3 : skipTwo i s (j-2+1)=s (j+1) := by simp [skipTwo,show ¬j-2+1 < i by omega,show j-2+1+2=j+1 by omega]
 rw [h0,h1,h2,h3,skipTwo_skipTwo hij]
 ring

end PolynomialVacuumAlgebra

end OAI

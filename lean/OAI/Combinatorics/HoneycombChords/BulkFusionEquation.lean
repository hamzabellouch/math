import OAI.Combinatorics.HoneycombChords.BoundaryFusionEquation
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Polynomial bulk fusion identities for the honeycomb strip transfer.
The identities intertwine the two-spin fusion map with the local operator. -/

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix BigOperators
noncomputable def qNumerator (r z : ℂ) : ℂ := (r^4*z^2+r^12)*(r^6*z^2+r^10)
noncomputable def bulkFusionLeft (r z : ℂ) (a b c j k : Fin 3) : ℂ :=
  qNumerator r z * ∑ u : Fin 3,∑ v : Fin 3,∑ m : Fin 3,
    rNumerator r (-z*r^14) 1 (b,c) (v,m)*
      rNumerator r (z*r^2) 1 (a,m) (u,k)*wNum r (u,v) j
noncomputable def bulkFusionRight (r z : ℂ) (a b c j k : Fin 3) : ℂ :=
  qNumerator r (z*r^2)*qNumerator r (-z*r^14)*
    ∑ f : Fin 3,wNum r (a,b) f*rNumerator r z 1 (f,c) (j,k)

private lemma bulkNumerator_eq_zero_of_sum_ne (r z w : ℂ) (p q : Pair)
    (h : p.1.val + p.2.val ≠ q.1.val + q.2.val) :
    rNumerator r z w p q = 0 := by
  unfold rNumerator
  split <;> simp_all

private lemma fusionNumerator_eq_zero_of_sum_ne (r : ℂ) (p : Pair) (j : Fin 3)
    (h : p.1.val + p.2.val ≠ j.val + 1) : wNum r p j = 0 := by
  unfold wNum
  split <;> simp_all

private lemma bulkFusionLeft_eq_zero_of_sum_ne (r z : ℂ) (a b c j k : Fin 3)
    (h : a.val + b.val + c.val ≠ j.val + k.val + 1) :
    bulkFusionLeft r z a b c j k = 0 := by
  unfold bulkFusionLeft
  suffices hs : (∑ u : Fin 3,∑ v : Fin 3,∑ m : Fin 3,
      rNumerator r (-z*r^14) 1 (b,c) (v,m)*
        rNumerator r (z*r^2) 1 (a,m) (u,k)*wNum r (u,v) j) = 0 by rw [hs,mul_zero]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro m _
  by_cases h₁ : b.val + c.val = v.val + m.val
  · by_cases h₂ : a.val + m.val = u.val + k.val
    · have h₃ : u.val + v.val ≠ j.val + 1 := by omega
      rw [fusionNumerator_eq_zero_of_sum_ne r (u,v) j h₃,mul_zero]
    · rw [bulkNumerator_eq_zero_of_sum_ne r (z*r^2) 1 (a,m) (u,k) h₂,mul_zero,zero_mul]
  · rw [bulkNumerator_eq_zero_of_sum_ne r (-z*r^14) 1 (b,c) (v,m) h₁,zero_mul,zero_mul]

private lemma bulkFusionRight_eq_zero_of_sum_ne (r z : ℂ) (a b c j k : Fin 3)
    (h : a.val + b.val + c.val ≠ j.val + k.val + 1) :
    bulkFusionRight r z a b c j k = 0 := by
  unfold bulkFusionRight
  suffices hs : (∑ f : Fin 3,wNum r (a,b) f*rNumerator r z 1 (f,c) (j,k))=0 by rw [hs,mul_zero]
  apply Finset.sum_eq_zero
  intro f _
  by_cases h₁ : a.val + b.val = f.val + 1
  · have h₂ : f.val + c.val ≠ j.val + k.val := by omega
    rw [bulkNumerator_eq_zero_of_sum_ne r z 1 (f,c) (j,k) h₂,mul_zero]
  · rw [fusionNumerator_eq_zero_of_sum_ne r (a,b) f h₁,zero_mul]

private abbrev bulkFusionAdd (a b : ℂ) : ℂ := a+b
private abbrev bulkFusionMul (a b : ℂ) : ℂ := a*b
private abbrev bulkFusionPow (a : ℂ) (n : ℕ) : ℂ := a^n
section
variable (r z : ℂ) (hr : r^16+1=0)

private lemma bulkFusionBulkComponent00000 : bulkFusionLeft r z 0 0 0 0 0 = bulkFusionRight r z 0 0 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 0 0 (by decide)]

private lemma bulkFusionBulkComponent00001 : bulkFusionLeft r z 0 0 0 0 1 = bulkFusionRight r z 0 0 0 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 0 1 (by decide)]

private lemma bulkFusionBulkComponent00002 : bulkFusionLeft r z 0 0 0 0 2 = bulkFusionRight r z 0 0 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 0 2 (by decide)]

private lemma bulkFusionBulkComponent00010 : bulkFusionLeft r z 0 0 0 1 0 = bulkFusionRight r z 0 0 0 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 1 0 (by decide)]

private lemma bulkFusionBulkComponent00011 : bulkFusionLeft r z 0 0 0 1 1 = bulkFusionRight r z 0 0 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 1 1 (by decide)]

private lemma bulkFusionBulkComponent00012 : bulkFusionLeft r z 0 0 0 1 2 = bulkFusionRight r z 0 0 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 1 2 (by decide)]

private lemma bulkFusionBulkComponent00020 : bulkFusionLeft r z 0 0 0 2 0 = bulkFusionRight r z 0 0 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 2 0 (by decide)]

private lemma bulkFusionBulkComponent00021 : bulkFusionLeft r z 0 0 0 2 1 = bulkFusionRight r z 0 0 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent00022 : bulkFusionLeft r z 0 0 0 2 2 = bulkFusionRight r z 0 0 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 0 2 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate00100 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent00100 : bulkFusionLeft r z 0 0 1 0 0 = bulkFusionRight r z 0 0 1 0 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate00100 r z*x) hr
  dsimp only [bulkFusionBulkCertificate00100,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent00101 : bulkFusionLeft r z 0 0 1 0 1 = bulkFusionRight r z 0 0 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 0 1 (by decide)]

private lemma bulkFusionBulkComponent00102 : bulkFusionLeft r z 0 0 1 0 2 = bulkFusionRight r z 0 0 1 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 0 2 (by decide)]

private lemma bulkFusionBulkComponent00110 : bulkFusionLeft r z 0 0 1 1 0 = bulkFusionRight r z 0 0 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 1 0 (by decide)]

private lemma bulkFusionBulkComponent00111 : bulkFusionLeft r z 0 0 1 1 1 = bulkFusionRight r z 0 0 1 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 1 1 (by decide)]

private lemma bulkFusionBulkComponent00112 : bulkFusionLeft r z 0 0 1 1 2 = bulkFusionRight r z 0 0 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 1 2 (by decide)]

private lemma bulkFusionBulkComponent00120 : bulkFusionLeft r z 0 0 1 2 0 = bulkFusionRight r z 0 0 1 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 2 0 (by decide)]

private lemma bulkFusionBulkComponent00121 : bulkFusionLeft r z 0 0 1 2 1 = bulkFusionRight r z 0 0 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 2 1 (by decide)]

private lemma bulkFusionBulkComponent00122 : bulkFusionLeft r z 0 0 1 2 2 = bulkFusionRight r z 0 0 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent00200 : bulkFusionLeft r z 0 0 2 0 0 = bulkFusionRight r z 0 0 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 0 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate00201 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (z)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (z)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent00201 : bulkFusionLeft r z 0 0 2 0 1 = bulkFusionRight r z 0 0 2 0 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate00201 r z*x) hr
  dsimp only [bulkFusionBulkCertificate00201,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent00202 : bulkFusionLeft r z 0 0 2 0 2 = bulkFusionRight r z 0 0 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 0 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate00210 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 126) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 122) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 118) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 118) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 12))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 6))) (bulkFusionMul ((-5:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 10))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 6))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 4)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionMul ((6:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 4))))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-5:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6))))))))
include hr in
private lemma bulkFusionBulkComponent00210 : bulkFusionLeft r z 0 0 2 1 0 = bulkFusionRight r z 0 0 2 1 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate00210 r z*x) hr
  dsimp only [bulkFusionBulkCertificate00210,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent00211 : bulkFusionLeft r z 0 0 2 1 1 = bulkFusionRight r z 0 0 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 1 1 (by decide)]

private lemma bulkFusionBulkComponent00212 : bulkFusionLeft r z 0 0 2 1 2 = bulkFusionRight r z 0 0 2 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 1 2 (by decide)]

private lemma bulkFusionBulkComponent00220 : bulkFusionLeft r z 0 0 2 2 0 = bulkFusionRight r z 0 0 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 2 0 (by decide)]

private lemma bulkFusionBulkComponent00221 : bulkFusionLeft r z 0 0 2 2 1 = bulkFusionRight r z 0 0 2 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 2 1 (by decide)]

private lemma bulkFusionBulkComponent00222 : bulkFusionLeft r z 0 0 2 2 2 = bulkFusionRight r z 0 0 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 0 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 0 2 2 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate01000 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 38)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent01000 : bulkFusionLeft r z 0 1 0 0 0 = bulkFusionRight r z 0 1 0 0 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate01000 r z*x) hr
  dsimp only [bulkFusionBulkCertificate01000,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent01001 : bulkFusionLeft r z 0 1 0 0 1 = bulkFusionRight r z 0 1 0 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 0 1 (by decide)]

private lemma bulkFusionBulkComponent01002 : bulkFusionLeft r z 0 1 0 0 2 = bulkFusionRight r z 0 1 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 0 2 (by decide)]

private lemma bulkFusionBulkComponent01010 : bulkFusionLeft r z 0 1 0 1 0 = bulkFusionRight r z 0 1 0 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 1 0 (by decide)]

private lemma bulkFusionBulkComponent01011 : bulkFusionLeft r z 0 1 0 1 1 = bulkFusionRight r z 0 1 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 1 1 (by decide)]

private lemma bulkFusionBulkComponent01012 : bulkFusionLeft r z 0 1 0 1 2 = bulkFusionRight r z 0 1 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 1 2 (by decide)]

private lemma bulkFusionBulkComponent01020 : bulkFusionLeft r z 0 1 0 2 0 = bulkFusionRight r z 0 1 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 2 0 (by decide)]

private lemma bulkFusionBulkComponent01021 : bulkFusionLeft r z 0 1 0 2 1 = bulkFusionRight r z 0 1 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent01022 : bulkFusionLeft r z 0 1 0 2 2 = bulkFusionRight r z 0 1 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent01100 : bulkFusionLeft r z 0 1 1 0 0 = bulkFusionRight r z 0 1 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 0 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate01101 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4)))))))
include hr in
private lemma bulkFusionBulkComponent01101 : bulkFusionLeft r z 0 1 1 0 1 = bulkFusionRight r z 0 1 1 0 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate01101 r z*x) hr
  dsimp only [bulkFusionBulkCertificate01101,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent01102 : bulkFusionLeft r z 0 1 1 0 2 = bulkFusionRight r z 0 1 1 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 0 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate01110 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 11)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (z)) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (z))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (z)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (z))) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent01110 : bulkFusionLeft r z 0 1 1 1 0 = bulkFusionRight r z 0 1 1 1 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate01110 r z*x) hr
  dsimp only [bulkFusionBulkCertificate01110,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent01111 : bulkFusionLeft r z 0 1 1 1 1 = bulkFusionRight r z 0 1 1 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 1 1 (by decide)]

private lemma bulkFusionBulkComponent01112 : bulkFusionLeft r z 0 1 1 1 2 = bulkFusionRight r z 0 1 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 1 2 (by decide)]

private lemma bulkFusionBulkComponent01120 : bulkFusionLeft r z 0 1 1 2 0 = bulkFusionRight r z 0 1 1 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 2 0 (by decide)]

private lemma bulkFusionBulkComponent01121 : bulkFusionLeft r z 0 1 1 2 1 = bulkFusionRight r z 0 1 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 2 1 (by decide)]

private lemma bulkFusionBulkComponent01122 : bulkFusionLeft r z 0 1 1 2 2 = bulkFusionRight r z 0 1 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent01200 : bulkFusionLeft r z 0 1 2 0 0 = bulkFusionRight r z 0 1 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent01201 : bulkFusionLeft r z 0 1 2 0 1 = bulkFusionRight r z 0 1 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 2 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate01202 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 30)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 18) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent01202 : bulkFusionLeft r z 0 1 2 0 2 = bulkFusionRight r z 0 1 2 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate01202 r z*x) hr
  dsimp only [bulkFusionBulkCertificate01202,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent01210 : bulkFusionLeft r z 0 1 2 1 0 = bulkFusionRight r z 0 1 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 2 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate01211 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 116) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 11)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent01211 : bulkFusionLeft r z 0 1 2 1 1 = bulkFusionRight r z 0 1 2 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate01211 r z*x) hr
  dsimp only [bulkFusionBulkCertificate01211,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent01212 : bulkFusionLeft r z 0 1 2 1 2 = bulkFusionRight r z 0 1 2 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 2 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 2 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate01220 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6))))))))
include hr in
private lemma bulkFusionBulkComponent01220 : bulkFusionLeft r z 0 1 2 2 0 = bulkFusionRight r z 0 1 2 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate01220 r z*x) hr
  dsimp only [bulkFusionBulkCertificate01220,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent01221 : bulkFusionLeft r z 0 1 2 2 1 = bulkFusionRight r z 0 1 2 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 2 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 2 2 1 (by decide)]

private lemma bulkFusionBulkComponent01222 : bulkFusionLeft r z 0 1 2 2 2 = bulkFusionRight r z 0 1 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 1 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 1 2 2 2 (by decide)]

private lemma bulkFusionBulkComponent02000 : bulkFusionLeft r z 0 2 0 0 0 = bulkFusionRight r z 0 2 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 0 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate02001 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((6:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (z)) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (z)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent02001 : bulkFusionLeft r z 0 2 0 0 1 = bulkFusionRight r z 0 2 0 0 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02001 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02001,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent02002 : bulkFusionLeft r z 0 2 0 0 2 = bulkFusionRight r z 0 2 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 0 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate02010 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 118) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 12)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 10))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))) (bulkFusionMul ((-5:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 46)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent02010 : bulkFusionLeft r z 0 2 0 1 0 = bulkFusionRight r z 0 2 0 1 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02010 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02010,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent02011 : bulkFusionLeft r z 0 2 0 1 1 = bulkFusionRight r z 0 2 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 1 1 (by decide)]

private lemma bulkFusionBulkComponent02012 : bulkFusionLeft r z 0 2 0 1 2 = bulkFusionRight r z 0 2 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 1 2 (by decide)]

private lemma bulkFusionBulkComponent02020 : bulkFusionLeft r z 0 2 0 2 0 = bulkFusionRight r z 0 2 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 2 0 (by decide)]

private lemma bulkFusionBulkComponent02021 : bulkFusionLeft r z 0 2 0 2 1 = bulkFusionRight r z 0 2 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent02022 : bulkFusionLeft r z 0 2 0 2 2 = bulkFusionRight r z 0 2 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent02100 : bulkFusionLeft r z 0 2 1 0 0 = bulkFusionRight r z 0 2 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 1 0 0 (by decide)]

private lemma bulkFusionBulkComponent02101 : bulkFusionLeft r z 0 2 1 0 1 = bulkFusionRight r z 0 2 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 1 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate02102 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent02102 : bulkFusionLeft r z 0 2 1 0 2 = bulkFusionRight r z 0 2 1 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02102 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02102,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  first | linear_combination hq | linear_combination -hq

private lemma bulkFusionBulkComponent02110 : bulkFusionLeft r z 0 2 1 1 0 = bulkFusionRight r z 0 2 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 1 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate02111 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8))) (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 4)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionPow r 62) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 46))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent02111 : bulkFusionLeft r z 0 2 1 1 1 = bulkFusionRight r z 0 2 1 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02111 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02111,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent02112 : bulkFusionLeft r z 0 2 1 1 2 = bulkFusionRight r z 0 2 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 1 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate02120 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 11))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 3)) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (z)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (z)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent02120 : bulkFusionLeft r z 0 2 1 2 0 = bulkFusionRight r z 0 2 1 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02120 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02120,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent02121 : bulkFusionLeft r z 0 2 1 2 1 = bulkFusionRight r z 0 2 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 1 2 1 (by decide)]

private lemma bulkFusionBulkComponent02122 : bulkFusionLeft r z 0 2 1 2 2 = bulkFusionRight r z 0 2 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent02200 : bulkFusionLeft r z 0 2 2 0 0 = bulkFusionRight r z 0 2 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent02201 : bulkFusionLeft r z 0 2 2 0 1 = bulkFusionRight r z 0 2 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 0 1 (by decide)]

private lemma bulkFusionBulkComponent02202 : bulkFusionLeft r z 0 2 2 0 2 = bulkFusionRight r z 0 2 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 0 2 (by decide)]

private lemma bulkFusionBulkComponent02210 : bulkFusionLeft r z 0 2 2 1 0 = bulkFusionRight r z 0 2 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 1 0 (by decide)]

private lemma bulkFusionBulkComponent02211 : bulkFusionLeft r z 0 2 2 1 1 = bulkFusionRight r z 0 2 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 1 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate02212 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 118) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 12))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 4)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 46)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent02212 : bulkFusionLeft r z 0 2 2 1 2 = bulkFusionRight r z 0 2 2 1 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02212 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02212,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  first | linear_combination hq | linear_combination -hq

private lemma bulkFusionBulkComponent02220 : bulkFusionLeft r z 0 2 2 2 0 = bulkFusionRight r z 0 2 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 2 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate02221 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 9))) (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 58) (z))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (z)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent02221 : bulkFusionLeft r z 0 2 2 2 1 = bulkFusionRight r z 0 2 2 2 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate02221 r z*x) hr
  dsimp only [bulkFusionBulkCertificate02221,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  first | linear_combination hq | linear_combination -hq

private lemma bulkFusionBulkComponent02222 : bulkFusionLeft r z 0 2 2 2 2 = bulkFusionRight r z 0 2 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 0 2 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 0 2 2 2 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate10000 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 38))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent10000 : bulkFusionLeft r z 1 0 0 0 0 = bulkFusionRight r z 1 0 0 0 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate10000 r z*x) hr
  dsimp only [bulkFusionBulkCertificate10000,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent10001 : bulkFusionLeft r z 1 0 0 0 1 = bulkFusionRight r z 1 0 0 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 0 1 (by decide)]

private lemma bulkFusionBulkComponent10002 : bulkFusionLeft r z 1 0 0 0 2 = bulkFusionRight r z 1 0 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 0 2 (by decide)]

private lemma bulkFusionBulkComponent10010 : bulkFusionLeft r z 1 0 0 1 0 = bulkFusionRight r z 1 0 0 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 1 0 (by decide)]

private lemma bulkFusionBulkComponent10011 : bulkFusionLeft r z 1 0 0 1 1 = bulkFusionRight r z 1 0 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 1 1 (by decide)]

private lemma bulkFusionBulkComponent10012 : bulkFusionLeft r z 1 0 0 1 2 = bulkFusionRight r z 1 0 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 1 2 (by decide)]

private lemma bulkFusionBulkComponent10020 : bulkFusionLeft r z 1 0 0 2 0 = bulkFusionRight r z 1 0 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 2 0 (by decide)]

private lemma bulkFusionBulkComponent10021 : bulkFusionLeft r z 1 0 0 2 1 = bulkFusionRight r z 1 0 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent10022 : bulkFusionLeft r z 1 0 0 2 2 = bulkFusionRight r z 1 0 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent10100 : bulkFusionLeft r z 1 0 1 0 0 = bulkFusionRight r z 1 0 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 0 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate10101 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))))))))
include hr in
private lemma bulkFusionBulkComponent10101 : bulkFusionLeft r z 1 0 1 0 1 = bulkFusionRight r z 1 0 1 0 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate10101 r z*x) hr
  dsimp only [bulkFusionBulkCertificate10101,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent10102 : bulkFusionLeft r z 1 0 1 0 2 = bulkFusionRight r z 1 0 1 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 0 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate10110 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (z))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent10110 : bulkFusionLeft r z 1 0 1 1 0 = bulkFusionRight r z 1 0 1 1 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate10110 r z*x) hr
  dsimp only [bulkFusionBulkCertificate10110,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent10111 : bulkFusionLeft r z 1 0 1 1 1 = bulkFusionRight r z 1 0 1 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 1 1 (by decide)]

private lemma bulkFusionBulkComponent10112 : bulkFusionLeft r z 1 0 1 1 2 = bulkFusionRight r z 1 0 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 1 2 (by decide)]

private lemma bulkFusionBulkComponent10120 : bulkFusionLeft r z 1 0 1 2 0 = bulkFusionRight r z 1 0 1 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 2 0 (by decide)]

private lemma bulkFusionBulkComponent10121 : bulkFusionLeft r z 1 0 1 2 1 = bulkFusionRight r z 1 0 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 2 1 (by decide)]

private lemma bulkFusionBulkComponent10122 : bulkFusionLeft r z 1 0 1 2 2 = bulkFusionRight r z 1 0 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent10200 : bulkFusionLeft r z 1 0 2 0 0 = bulkFusionRight r z 1 0 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent10201 : bulkFusionLeft r z 1 0 2 0 1 = bulkFusionRight r z 1 0 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 2 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate10202 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 30)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 18) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent10202 : bulkFusionLeft r z 1 0 2 0 2 = bulkFusionRight r z 1 0 2 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate10202 r z*x) hr
  dsimp only [bulkFusionBulkCertificate10202,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent10210 : bulkFusionLeft r z 1 0 2 1 0 = bulkFusionRight r z 1 0 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 2 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate10211 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 124) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 120) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 116) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 116) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 116) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 11))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 11)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9))) (bulkFusionMul ((4:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 80) (z)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 72) (z)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 9)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (z))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 48) (z)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 40) (z))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent10211 : bulkFusionLeft r z 1 0 2 1 1 = bulkFusionRight r z 1 0 2 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate10211 r z*x) hr
  dsimp only [bulkFusionBulkCertificate10211,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent10212 : bulkFusionLeft r z 1 0 2 1 2 = bulkFusionRight r z 1 0 2 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 2 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 2 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate10220 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4)) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent10220 : bulkFusionLeft r z 1 0 2 2 0 = bulkFusionRight r z 1 0 2 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate10220 r z*x) hr
  dsimp only [bulkFusionBulkCertificate10220,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent10221 : bulkFusionLeft r z 1 0 2 2 1 = bulkFusionRight r z 1 0 2 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 2 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 2 2 1 (by decide)]

private lemma bulkFusionBulkComponent10222 : bulkFusionLeft r z 1 0 2 2 2 = bulkFusionRight r z 1 0 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 0 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 0 2 2 2 (by decide)]

private lemma bulkFusionBulkComponent11000 : bulkFusionLeft r z 1 1 0 0 0 = bulkFusionRight r z 1 1 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 0 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate11001 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 5)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 11))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent11001 : bulkFusionLeft r z 1 1 0 0 1 = bulkFusionRight r z 1 1 0 0 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11001 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11001,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11002 : bulkFusionLeft r z 1 1 0 0 2 = bulkFusionRight r z 1 1 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 0 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate11010 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 10)) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 48)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 4))) (bulkFusionPow r 36)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 24) (bulkFusionPow z 4)))))))
include hr in
private lemma bulkFusionBulkComponent11010 : bulkFusionLeft r z 1 1 0 1 0 = bulkFusionRight r z 1 1 0 1 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11010 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11010,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11011 : bulkFusionLeft r z 1 1 0 1 1 = bulkFusionRight r z 1 1 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 1 1 (by decide)]

private lemma bulkFusionBulkComponent11012 : bulkFusionLeft r z 1 1 0 1 2 = bulkFusionRight r z 1 1 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 1 2 (by decide)]

private lemma bulkFusionBulkComponent11020 : bulkFusionLeft r z 1 1 0 2 0 = bulkFusionRight r z 1 1 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 2 0 (by decide)]

private lemma bulkFusionBulkComponent11021 : bulkFusionLeft r z 1 1 0 2 1 = bulkFusionRight r z 1 1 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent11022 : bulkFusionLeft r z 1 1 0 2 2 = bulkFusionRight r z 1 1 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent11100 : bulkFusionLeft r z 1 1 1 0 0 = bulkFusionRight r z 1 1 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 1 0 0 (by decide)]

private lemma bulkFusionBulkComponent11101 : bulkFusionLeft r z 1 1 1 0 1 = bulkFusionRight r z 1 1 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 1 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate11102 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 11))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (z))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (z))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent11102 : bulkFusionLeft r z 1 1 1 0 2 = bulkFusionRight r z 1 1 1 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11102 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11102,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11110 : bulkFusionLeft r z 1 1 1 1 0 = bulkFusionRight r z 1 1 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 1 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate11111 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 8))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 6)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 8)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 6)))))))
include hr in
private lemma bulkFusionBulkComponent11111 : bulkFusionLeft r z 1 1 1 1 1 = bulkFusionRight r z 1 1 1 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11111 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11111,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11112 : bulkFusionLeft r z 1 1 1 1 2 = bulkFusionRight r z 1 1 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 1 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate11120 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 66) (z)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (z)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent11120 : bulkFusionLeft r z 1 1 1 2 0 = bulkFusionRight r z 1 1 1 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11120 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11120,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11121 : bulkFusionLeft r z 1 1 1 2 1 = bulkFusionRight r z 1 1 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 1 2 1 (by decide)]

private lemma bulkFusionBulkComponent11122 : bulkFusionLeft r z 1 1 1 2 2 = bulkFusionRight r z 1 1 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent11200 : bulkFusionLeft r z 1 1 2 0 0 = bulkFusionRight r z 1 1 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent11201 : bulkFusionLeft r z 1 1 2 0 1 = bulkFusionRight r z 1 1 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 0 1 (by decide)]

private lemma bulkFusionBulkComponent11202 : bulkFusionLeft r z 1 1 2 0 2 = bulkFusionRight r z 1 1 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 0 2 (by decide)]

private lemma bulkFusionBulkComponent11210 : bulkFusionLeft r z 1 1 2 1 0 = bulkFusionRight r z 1 1 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 1 0 (by decide)]

private lemma bulkFusionBulkComponent11211 : bulkFusionLeft r z 1 1 2 1 1 = bulkFusionRight r z 1 1 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 1 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate11212 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 10)) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 48)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 4))) (bulkFusionPow r 36)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 24) (bulkFusionPow z 4)))))))
include hr in
private lemma bulkFusionBulkComponent11212 : bulkFusionLeft r z 1 1 2 1 2 = bulkFusionRight r z 1 1 2 1 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11212 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11212,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11220 : bulkFusionLeft r z 1 1 2 2 0 = bulkFusionRight r z 1 1 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 2 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate11221 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 5)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 11))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent11221 : bulkFusionLeft r z 1 1 2 2 1 = bulkFusionRight r z 1 1 2 2 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate11221 r z*x) hr
  dsimp only [bulkFusionBulkCertificate11221,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent11222 : bulkFusionLeft r z 1 1 2 2 2 = bulkFusionRight r z 1 1 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 1 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 1 2 2 2 (by decide)]

private lemma bulkFusionBulkComponent12000 : bulkFusionLeft r z 1 2 0 0 0 = bulkFusionRight r z 1 2 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 0 0 0 (by decide)]

private lemma bulkFusionBulkComponent12001 : bulkFusionLeft r z 1 2 0 0 1 = bulkFusionRight r z 1 2 0 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 0 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 0 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate12002 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionPow r 38))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent12002 : bulkFusionLeft r z 1 2 0 0 2 = bulkFusionRight r z 1 2 0 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate12002 r z*x) hr
  dsimp only [bulkFusionBulkCertificate12002,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent12010 : bulkFusionLeft r z 1 2 0 1 0 = bulkFusionRight r z 1 2 0 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 0 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 0 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate12011 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 116) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 112) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 11))) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 11)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 9))))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (z))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (z))) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 60) (z))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7)) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 56) (z)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 9)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 52) (z)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 48) (z)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent12011 : bulkFusionLeft r z 1 2 0 1 1 = bulkFusionRight r z 1 2 0 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate12011 r z*x) hr
  dsimp only [bulkFusionBulkCertificate12011,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent12012 : bulkFusionLeft r z 1 2 0 1 2 = bulkFusionRight r z 1 2 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 0 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate12020 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 30)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 18) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent12020 : bulkFusionLeft r z 1 2 0 2 0 = bulkFusionRight r z 1 2 0 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate12020 r z*x) hr
  dsimp only [bulkFusionBulkCertificate12020,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent12021 : bulkFusionLeft r z 1 2 0 2 1 = bulkFusionRight r z 1 2 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent12022 : bulkFusionLeft r z 1 2 0 2 2 = bulkFusionRight r z 1 2 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent12100 : bulkFusionLeft r z 1 2 1 0 0 = bulkFusionRight r z 1 2 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 0 0 (by decide)]

private lemma bulkFusionBulkComponent12101 : bulkFusionLeft r z 1 2 1 0 1 = bulkFusionRight r z 1 2 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 0 1 (by decide)]

private lemma bulkFusionBulkComponent12102 : bulkFusionLeft r z 1 2 1 0 2 = bulkFusionRight r z 1 2 1 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 0 2 (by decide)]

private lemma bulkFusionBulkComponent12110 : bulkFusionLeft r z 1 2 1 1 0 = bulkFusionRight r z 1 2 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 1 0 (by decide)]

private lemma bulkFusionBulkComponent12111 : bulkFusionLeft r z 1 2 1 1 1 = bulkFusionRight r z 1 2 1 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 1 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate12112 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (z))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent12112 : bulkFusionLeft r z 1 2 1 1 2 = bulkFusionRight r z 1 2 1 1 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate12112 r z*x) hr
  dsimp only [bulkFusionBulkCertificate12112,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent12120 : bulkFusionLeft r z 1 2 1 2 0 = bulkFusionRight r z 1 2 1 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 2 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate12121 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))))))))
include hr in
private lemma bulkFusionBulkComponent12121 : bulkFusionLeft r z 1 2 1 2 1 = bulkFusionRight r z 1 2 1 2 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate12121 r z*x) hr
  dsimp only [bulkFusionBulkCertificate12121,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent12122 : bulkFusionLeft r z 1 2 1 2 2 = bulkFusionRight r z 1 2 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent12200 : bulkFusionLeft r z 1 2 2 0 0 = bulkFusionRight r z 1 2 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent12201 : bulkFusionLeft r z 1 2 2 0 1 = bulkFusionRight r z 1 2 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 0 1 (by decide)]

private lemma bulkFusionBulkComponent12202 : bulkFusionLeft r z 1 2 2 0 2 = bulkFusionRight r z 1 2 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 0 2 (by decide)]

private lemma bulkFusionBulkComponent12210 : bulkFusionLeft r z 1 2 2 1 0 = bulkFusionRight r z 1 2 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 1 0 (by decide)]

private lemma bulkFusionBulkComponent12211 : bulkFusionLeft r z 1 2 2 1 1 = bulkFusionRight r z 1 2 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 1 1 (by decide)]

private lemma bulkFusionBulkComponent12212 : bulkFusionLeft r z 1 2 2 1 2 = bulkFusionRight r z 1 2 2 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 1 2 (by decide)]

private lemma bulkFusionBulkComponent12220 : bulkFusionLeft r z 1 2 2 2 0 = bulkFusionRight r z 1 2 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 2 0 (by decide)]

private lemma bulkFusionBulkComponent12221 : bulkFusionLeft r z 1 2 2 2 1 = bulkFusionRight r z 1 2 2 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 1 2 2 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 1 2 2 2 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate12222 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 38))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent12222 : bulkFusionLeft r z 1 2 2 2 2 = bulkFusionRight r z 1 2 2 2 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate12222 r z*x) hr
  dsimp only [bulkFusionBulkCertificate12222,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20000 : bulkFusionLeft r z 2 0 0 0 0 = bulkFusionRight r z 2 0 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 0 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate20001 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 9))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 9)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (z)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent20001 : bulkFusionLeft r z 2 0 0 0 1 = bulkFusionRight r z 2 0 0 0 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20001 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20001,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20002 : bulkFusionLeft r z 2 0 0 0 2 = bulkFusionRight r z 2 0 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 0 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate20010 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 12)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionPow r 38) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4)))))))
include hr in
private lemma bulkFusionBulkComponent20010 : bulkFusionLeft r z 2 0 0 1 0 = bulkFusionRight r z 2 0 0 1 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20010 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20010,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20011 : bulkFusionLeft r z 2 0 0 1 1 = bulkFusionRight r z 2 0 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 1 1 (by decide)]

private lemma bulkFusionBulkComponent20012 : bulkFusionLeft r z 2 0 0 1 2 = bulkFusionRight r z 2 0 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 1 2 (by decide)]

private lemma bulkFusionBulkComponent20020 : bulkFusionLeft r z 2 0 0 2 0 = bulkFusionRight r z 2 0 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 2 0 (by decide)]

private lemma bulkFusionBulkComponent20021 : bulkFusionLeft r z 2 0 0 2 1 = bulkFusionRight r z 2 0 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent20022 : bulkFusionLeft r z 2 0 0 2 2 = bulkFusionRight r z 2 0 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent20100 : bulkFusionLeft r z 2 0 1 0 0 = bulkFusionRight r z 2 0 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 1 0 0 (by decide)]

private lemma bulkFusionBulkComponent20101 : bulkFusionLeft r z 2 0 1 0 1 = bulkFusionRight r z 2 0 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 1 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate20102 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3)) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (z))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent20102 : bulkFusionLeft r z 2 0 1 0 2 = bulkFusionRight r z 2 0 1 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20102 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20102,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20110 : bulkFusionLeft r z 2 0 1 1 0 = bulkFusionRight r z 2 0 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 1 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate20111 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 54)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 8))) (bulkFusionPow r 38)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4)))))))
include hr in
private lemma bulkFusionBulkComponent20111 : bulkFusionLeft r z 2 0 1 1 1 = bulkFusionRight r z 2 0 1 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20111 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20111,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20112 : bulkFusionLeft r z 2 0 1 1 2 = bulkFusionRight r z 2 0 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 1 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate20120 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent20120 : bulkFusionLeft r z 2 0 1 2 0 = bulkFusionRight r z 2 0 1 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20120 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20120,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  first | linear_combination hq | linear_combination -hq

private lemma bulkFusionBulkComponent20121 : bulkFusionLeft r z 2 0 1 2 1 = bulkFusionRight r z 2 0 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 1 2 1 (by decide)]

private lemma bulkFusionBulkComponent20122 : bulkFusionLeft r z 2 0 1 2 2 = bulkFusionRight r z 2 0 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent20200 : bulkFusionLeft r z 2 0 2 0 0 = bulkFusionRight r z 2 0 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent20201 : bulkFusionLeft r z 2 0 2 0 1 = bulkFusionRight r z 2 0 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 0 1 (by decide)]

private lemma bulkFusionBulkComponent20202 : bulkFusionLeft r z 2 0 2 0 2 = bulkFusionRight r z 2 0 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 0 2 (by decide)]

private lemma bulkFusionBulkComponent20210 : bulkFusionLeft r z 2 0 2 1 0 = bulkFusionRight r z 2 0 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 1 0 (by decide)]

private lemma bulkFusionBulkComponent20211 : bulkFusionLeft r z 2 0 2 1 1 = bulkFusionRight r z 2 0 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 1 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate20212 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 122) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 118) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 118) (bulkFusionPow z 6))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-6:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 8))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-5:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 4))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 12))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 4))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8)) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((5:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8)) (bulkFusionMul ((5:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6)) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionPow r 38) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent20212 : bulkFusionLeft r z 2 0 2 1 2 = bulkFusionRight r z 2 0 2 1 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20212 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20212,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20220 : bulkFusionLeft r z 2 0 2 2 0 = bulkFusionRight r z 2 0 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 2 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate20221 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 9))) (bulkFusionMul ((-5:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 7))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 9)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent20221 : bulkFusionLeft r z 2 0 2 2 1 = bulkFusionRight r z 2 0 2 2 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate20221 r z*x) hr
  dsimp only [bulkFusionBulkCertificate20221,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent20222 : bulkFusionLeft r z 2 0 2 2 2 = bulkFusionRight r z 2 0 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 0 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 0 2 2 2 (by decide)]

private lemma bulkFusionBulkComponent21000 : bulkFusionLeft r z 2 1 0 0 0 = bulkFusionRight r z 2 1 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 0 0 0 (by decide)]

private lemma bulkFusionBulkComponent21001 : bulkFusionLeft r z 2 1 0 0 1 = bulkFusionRight r z 2 1 0 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 0 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 0 0 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate21002 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 8))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionPow r 38))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent21002 : bulkFusionLeft r z 2 1 0 0 2 = bulkFusionRight r z 2 1 0 0 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate21002 r z*x) hr
  dsimp only [bulkFusionBulkCertificate21002,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent21010 : bulkFusionLeft r z 2 1 0 1 0 = bulkFusionRight r z 2 1 0 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 0 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 0 1 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate21011 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 108) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 104) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 100) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 11))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 9)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 96) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 92) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 11))) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 7))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 48) (z)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 40) (z)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent21011 : bulkFusionLeft r z 2 1 0 1 1 = bulkFusionRight r z 2 1 0 1 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate21011 r z*x) hr
  dsimp only [bulkFusionBulkCertificate21011,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent21012 : bulkFusionLeft r z 2 1 0 1 2 = bulkFusionRight r z 2 1 0 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 0 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 0 1 2 (by decide)]

private noncomputable def bulkFusionBulkCertificate21020 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 2))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 8)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 4)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 30)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 2))))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 18) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent21020 : bulkFusionLeft r z 2 1 0 2 0 = bulkFusionRight r z 2 1 0 2 0 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate21020 r z*x) hr
  dsimp only [bulkFusionBulkCertificate21020,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent21021 : bulkFusionLeft r z 2 1 0 2 1 = bulkFusionRight r z 2 1 0 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 0 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 0 2 1 (by decide)]

private lemma bulkFusionBulkComponent21022 : bulkFusionLeft r z 2 1 0 2 2 = bulkFusionRight r z 2 1 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent21100 : bulkFusionLeft r z 2 1 1 0 0 = bulkFusionRight r z 2 1 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 0 0 (by decide)]

private lemma bulkFusionBulkComponent21101 : bulkFusionLeft r z 2 1 1 0 1 = bulkFusionRight r z 2 1 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 0 1 (by decide)]

private lemma bulkFusionBulkComponent21102 : bulkFusionLeft r z 2 1 1 0 2 = bulkFusionRight r z 2 1 1 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 0 2 (by decide)]

private lemma bulkFusionBulkComponent21110 : bulkFusionLeft r z 2 1 1 1 0 = bulkFusionRight r z 2 1 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 1 0 (by decide)]

private lemma bulkFusionBulkComponent21111 : bulkFusionLeft r z 2 1 1 1 1 = bulkFusionRight r z 2 1 1 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 1 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate21112 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 7))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 5))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 11))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 7)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9)) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 5))) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (z))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 7)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (z))) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 5))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (z)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 3)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent21112 : bulkFusionLeft r z 2 1 1 1 2 = bulkFusionRight r z 2 1 1 1 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate21112 r z*x) hr
  dsimp only [bulkFusionBulkCertificate21112,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent21120 : bulkFusionLeft r z 2 1 1 2 0 = bulkFusionRight r z 2 1 1 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 2 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate21121 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4)))))))
include hr in
private lemma bulkFusionBulkComponent21121 : bulkFusionLeft r z 2 1 1 2 1 = bulkFusionRight r z 2 1 1 2 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate21121 r z*x) hr
  dsimp only [bulkFusionBulkCertificate21121,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent21122 : bulkFusionLeft r z 2 1 1 2 2 = bulkFusionRight r z 2 1 1 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 1 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 1 2 2 (by decide)]

private lemma bulkFusionBulkComponent21200 : bulkFusionLeft r z 2 1 2 0 0 = bulkFusionRight r z 2 1 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent21201 : bulkFusionLeft r z 2 1 2 0 1 = bulkFusionRight r z 2 1 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 0 1 (by decide)]

private lemma bulkFusionBulkComponent21202 : bulkFusionLeft r z 2 1 2 0 2 = bulkFusionRight r z 2 1 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 0 2 (by decide)]

private lemma bulkFusionBulkComponent21210 : bulkFusionLeft r z 2 1 2 1 0 = bulkFusionRight r z 2 1 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 1 0 (by decide)]

private lemma bulkFusionBulkComponent21211 : bulkFusionLeft r z 2 1 2 1 1 = bulkFusionRight r z 2 1 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 1 1 (by decide)]

private lemma bulkFusionBulkComponent21212 : bulkFusionLeft r z 2 1 2 1 2 = bulkFusionRight r z 2 1 2 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 1 2 (by decide)]

private lemma bulkFusionBulkComponent21220 : bulkFusionLeft r z 2 1 2 2 0 = bulkFusionRight r z 2 1 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 2 0 (by decide)]

private lemma bulkFusionBulkComponent21221 : bulkFusionLeft r z 2 1 2 2 1 = bulkFusionRight r z 2 1 2 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 1 2 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 1 2 2 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate21222 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 10)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))) (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-3:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionPow r 38)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 6))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 2))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 4))))))))
include hr in
private lemma bulkFusionBulkComponent21222 : bulkFusionLeft r z 2 1 2 2 2 = bulkFusionRight r z 2 1 2 2 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate21222 r z*x) hr
  dsimp only [bulkFusionBulkCertificate21222,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent22000 : bulkFusionLeft r z 2 2 0 0 0 = bulkFusionRight r z 2 2 0 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 0 0 (by decide)]

private lemma bulkFusionBulkComponent22001 : bulkFusionLeft r z 2 2 0 0 1 = bulkFusionRight r z 2 2 0 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 0 1 (by decide)]

private lemma bulkFusionBulkComponent22002 : bulkFusionLeft r z 2 2 0 0 2 = bulkFusionRight r z 2 2 0 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 0 2 (by decide)]

private lemma bulkFusionBulkComponent22010 : bulkFusionLeft r z 2 2 0 1 0 = bulkFusionRight r z 2 2 0 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 1 0 (by decide)]

private lemma bulkFusionBulkComponent22011 : bulkFusionLeft r z 2 2 0 1 1 = bulkFusionRight r z 2 2 0 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 1 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate22012 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 114) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 110) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 106) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 102) (bulkFusionPow z 6))) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 10)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 8)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 10))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 10))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 4)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 10)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 4))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 10))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 4))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 8)))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 6))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 4)))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-4:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 6))) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 4))))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 8))) (bulkFusionAdd (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 2))) (bulkFusionMul ((-2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 8)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 2)))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 8))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 6)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 4))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 2))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 6)) (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 2))) (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 8))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 6)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 2)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 6)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((3:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 4))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 2)) (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 6))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((2:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 4))) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 6))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 4)) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 6)))))))
include hr in
private lemma bulkFusionBulkComponent22012 : bulkFusionLeft r z 2 2 0 1 2 = bulkFusionRight r z 2 2 0 1 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate22012 r z*x) hr
  dsimp only [bulkFusionBulkCertificate22012,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent22020 : bulkFusionLeft r z 2 2 0 2 0 = bulkFusionRight r z 2 2 0 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 2 0 (by decide)]

private noncomputable def bulkFusionBulkCertificate22021 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 98) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 94) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 90) (bulkFusionPow z 9))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 11)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 86) (bulkFusionPow z 5)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 82) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 11))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 78) (bulkFusionPow z 7)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 74) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 7))) (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 70) (bulkFusionPow z 3)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 66) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 9))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 5)) (bulkFusionMul (bulkFusionPow r 62) (bulkFusionPow z 3))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 9)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 58) (bulkFusionPow z 3))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 54) (bulkFusionPow z 9))) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 7)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 50) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 7))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 46) (bulkFusionPow z 3)) (bulkFusionMul (bulkFusionPow r 42) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 42) (z))) (bulkFusionMul (bulkFusionPow r 38) (bulkFusionPow z 5))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 5)) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 34) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 30) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 7)) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 26) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 22) (bulkFusionPow z 5))))))))
include hr in
private lemma bulkFusionBulkComponent22021 : bulkFusionLeft r z 2 2 0 2 1 = bulkFusionRight r z 2 2 0 2 1 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate22021 r z*x) hr
  dsimp only [bulkFusionBulkCertificate22021,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent22022 : bulkFusionLeft r z 2 2 0 2 2 = bulkFusionRight r z 2 2 0 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 0 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 0 2 2 (by decide)]

private lemma bulkFusionBulkComponent22100 : bulkFusionLeft r z 2 2 1 0 0 = bulkFusionRight r z 2 2 1 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 0 0 (by decide)]

private lemma bulkFusionBulkComponent22101 : bulkFusionLeft r z 2 2 1 0 1 = bulkFusionRight r z 2 2 1 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 0 1 (by decide)]

private lemma bulkFusionBulkComponent22102 : bulkFusionLeft r z 2 2 1 0 2 = bulkFusionRight r z 2 2 1 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 0 2 (by decide)]

private lemma bulkFusionBulkComponent22110 : bulkFusionLeft r z 2 2 1 1 0 = bulkFusionRight r z 2 2 1 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 1 0 (by decide)]

private lemma bulkFusionBulkComponent22111 : bulkFusionLeft r z 2 2 1 1 1 = bulkFusionRight r z 2 2 1 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 1 1 (by decide)]

private lemma bulkFusionBulkComponent22112 : bulkFusionLeft r z 2 2 1 1 2 = bulkFusionRight r z 2 2 1 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 1 2 (by decide)]

private lemma bulkFusionBulkComponent22120 : bulkFusionLeft r z 2 2 1 2 0 = bulkFusionRight r z 2 2 1 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 2 0 (by decide)]

private lemma bulkFusionBulkComponent22121 : bulkFusionLeft r z 2 2 1 2 1 = bulkFusionRight r z 2 2 1 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 1 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 1 2 1 (by decide)]

private noncomputable def bulkFusionBulkCertificate22122 (r z : ℂ) : ℂ :=
  bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 88) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 84) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 5))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 80) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 9)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 76) (bulkFusionPow z 5)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 72) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 9))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 7))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 68) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 64) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 60) (bulkFusionPow z 7))))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 56) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 52) (bulkFusionPow z 5)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (bulkFusionPow z 3))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 48) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 7)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 44) (bulkFusionPow z 3)))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 40) (z))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 7))))) (bulkFusionAdd (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 5))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 36) (bulkFusionPow z 3)))) (bulkFusionAdd (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 32) (bulkFusionPow z 3))) (bulkFusionMul ((-1:ℂ)) (bulkFusionMul (bulkFusionPow r 28) (bulkFusionPow z 5)))))))
include hr in
private lemma bulkFusionBulkComponent22122 : bulkFusionLeft r z 2 2 1 2 2 = bulkFusionRight r z 2 2 1 2 2 := by
  simp [bulkFusionLeft,bulkFusionRight,Fin.sum_univ_three,rNumerator,wNum,qNumerator,-mul_eq_zero]
  have hq:=congrArg (fun x : ℂ=>bulkFusionBulkCertificate22122 r z*x) hr
  dsimp only [bulkFusionBulkCertificate22122,bulkFusionAdd,bulkFusionMul,bulkFusionPow] at hq
  linear_combination hq

private lemma bulkFusionBulkComponent22200 : bulkFusionLeft r z 2 2 2 0 0 = bulkFusionRight r z 2 2 2 0 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 0 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 0 0 (by decide)]

private lemma bulkFusionBulkComponent22201 : bulkFusionLeft r z 2 2 2 0 1 = bulkFusionRight r z 2 2 2 0 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 0 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 0 1 (by decide)]

private lemma bulkFusionBulkComponent22202 : bulkFusionLeft r z 2 2 2 0 2 = bulkFusionRight r z 2 2 2 0 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 0 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 0 2 (by decide)]

private lemma bulkFusionBulkComponent22210 : bulkFusionLeft r z 2 2 2 1 0 = bulkFusionRight r z 2 2 2 1 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 1 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 1 0 (by decide)]

private lemma bulkFusionBulkComponent22211 : bulkFusionLeft r z 2 2 2 1 1 = bulkFusionRight r z 2 2 2 1 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 1 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 1 1 (by decide)]

private lemma bulkFusionBulkComponent22212 : bulkFusionLeft r z 2 2 2 1 2 = bulkFusionRight r z 2 2 2 1 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 1 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 1 2 (by decide)]

private lemma bulkFusionBulkComponent22220 : bulkFusionLeft r z 2 2 2 2 0 = bulkFusionRight r z 2 2 2 2 0 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 2 0 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 2 0 (by decide)]

private lemma bulkFusionBulkComponent22221 : bulkFusionLeft r z 2 2 2 2 1 = bulkFusionRight r z 2 2 2 2 1 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 2 1 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 2 1 (by decide)]

private lemma bulkFusionBulkComponent22222 : bulkFusionLeft r z 2 2 2 2 2 = bulkFusionRight r z 2 2 2 2 2 := by
  rw [bulkFusionLeft_eq_zero_of_sum_ne r z 2 2 2 2 2 (by decide),
    bulkFusionRight_eq_zero_of_sum_ne r z 2 2 2 2 2 (by decide)]

include hr in
theorem bulk_fusion_numerator (a b c j k : Fin 3) : bulkFusionLeft r z a b c j k=bulkFusionRight r z a b c j k := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases j <;> fin_cases k
  · exact bulkFusionBulkComponent00000 r z
  · exact bulkFusionBulkComponent00001 r z
  · exact bulkFusionBulkComponent00002 r z
  · exact bulkFusionBulkComponent00010 r z
  · exact bulkFusionBulkComponent00011 r z
  · exact bulkFusionBulkComponent00012 r z
  · exact bulkFusionBulkComponent00020 r z
  · exact bulkFusionBulkComponent00021 r z
  · exact bulkFusionBulkComponent00022 r z
  · exact bulkFusionBulkComponent00100 r z hr
  · exact bulkFusionBulkComponent00101 r z
  · exact bulkFusionBulkComponent00102 r z
  · exact bulkFusionBulkComponent00110 r z
  · exact bulkFusionBulkComponent00111 r z
  · exact bulkFusionBulkComponent00112 r z
  · exact bulkFusionBulkComponent00120 r z
  · exact bulkFusionBulkComponent00121 r z
  · exact bulkFusionBulkComponent00122 r z
  · exact bulkFusionBulkComponent00200 r z
  · exact bulkFusionBulkComponent00201 r z hr
  · exact bulkFusionBulkComponent00202 r z
  · exact bulkFusionBulkComponent00210 r z hr
  · exact bulkFusionBulkComponent00211 r z
  · exact bulkFusionBulkComponent00212 r z
  · exact bulkFusionBulkComponent00220 r z
  · exact bulkFusionBulkComponent00221 r z
  · exact bulkFusionBulkComponent00222 r z
  · exact bulkFusionBulkComponent01000 r z hr
  · exact bulkFusionBulkComponent01001 r z
  · exact bulkFusionBulkComponent01002 r z
  · exact bulkFusionBulkComponent01010 r z
  · exact bulkFusionBulkComponent01011 r z
  · exact bulkFusionBulkComponent01012 r z
  · exact bulkFusionBulkComponent01020 r z
  · exact bulkFusionBulkComponent01021 r z
  · exact bulkFusionBulkComponent01022 r z
  · exact bulkFusionBulkComponent01100 r z
  · exact bulkFusionBulkComponent01101 r z hr
  · exact bulkFusionBulkComponent01102 r z
  · exact bulkFusionBulkComponent01110 r z hr
  · exact bulkFusionBulkComponent01111 r z
  · exact bulkFusionBulkComponent01112 r z
  · exact bulkFusionBulkComponent01120 r z
  · exact bulkFusionBulkComponent01121 r z
  · exact bulkFusionBulkComponent01122 r z
  · exact bulkFusionBulkComponent01200 r z
  · exact bulkFusionBulkComponent01201 r z
  · exact bulkFusionBulkComponent01202 r z hr
  · exact bulkFusionBulkComponent01210 r z
  · exact bulkFusionBulkComponent01211 r z hr
  · exact bulkFusionBulkComponent01212 r z
  · exact bulkFusionBulkComponent01220 r z hr
  · exact bulkFusionBulkComponent01221 r z
  · exact bulkFusionBulkComponent01222 r z
  · exact bulkFusionBulkComponent02000 r z
  · exact bulkFusionBulkComponent02001 r z hr
  · exact bulkFusionBulkComponent02002 r z
  · exact bulkFusionBulkComponent02010 r z hr
  · exact bulkFusionBulkComponent02011 r z
  · exact bulkFusionBulkComponent02012 r z
  · exact bulkFusionBulkComponent02020 r z
  · exact bulkFusionBulkComponent02021 r z
  · exact bulkFusionBulkComponent02022 r z
  · exact bulkFusionBulkComponent02100 r z
  · exact bulkFusionBulkComponent02101 r z
  · exact bulkFusionBulkComponent02102 r z hr
  · exact bulkFusionBulkComponent02110 r z
  · exact bulkFusionBulkComponent02111 r z hr
  · exact bulkFusionBulkComponent02112 r z
  · exact bulkFusionBulkComponent02120 r z hr
  · exact bulkFusionBulkComponent02121 r z
  · exact bulkFusionBulkComponent02122 r z
  · exact bulkFusionBulkComponent02200 r z
  · exact bulkFusionBulkComponent02201 r z
  · exact bulkFusionBulkComponent02202 r z
  · exact bulkFusionBulkComponent02210 r z
  · exact bulkFusionBulkComponent02211 r z
  · exact bulkFusionBulkComponent02212 r z hr
  · exact bulkFusionBulkComponent02220 r z
  · exact bulkFusionBulkComponent02221 r z hr
  · exact bulkFusionBulkComponent02222 r z
  · exact bulkFusionBulkComponent10000 r z hr
  · exact bulkFusionBulkComponent10001 r z
  · exact bulkFusionBulkComponent10002 r z
  · exact bulkFusionBulkComponent10010 r z
  · exact bulkFusionBulkComponent10011 r z
  · exact bulkFusionBulkComponent10012 r z
  · exact bulkFusionBulkComponent10020 r z
  · exact bulkFusionBulkComponent10021 r z
  · exact bulkFusionBulkComponent10022 r z
  · exact bulkFusionBulkComponent10100 r z
  · exact bulkFusionBulkComponent10101 r z hr
  · exact bulkFusionBulkComponent10102 r z
  · exact bulkFusionBulkComponent10110 r z hr
  · exact bulkFusionBulkComponent10111 r z
  · exact bulkFusionBulkComponent10112 r z
  · exact bulkFusionBulkComponent10120 r z
  · exact bulkFusionBulkComponent10121 r z
  · exact bulkFusionBulkComponent10122 r z
  · exact bulkFusionBulkComponent10200 r z
  · exact bulkFusionBulkComponent10201 r z
  · exact bulkFusionBulkComponent10202 r z hr
  · exact bulkFusionBulkComponent10210 r z
  · exact bulkFusionBulkComponent10211 r z hr
  · exact bulkFusionBulkComponent10212 r z
  · exact bulkFusionBulkComponent10220 r z hr
  · exact bulkFusionBulkComponent10221 r z
  · exact bulkFusionBulkComponent10222 r z
  · exact bulkFusionBulkComponent11000 r z
  · exact bulkFusionBulkComponent11001 r z hr
  · exact bulkFusionBulkComponent11002 r z
  · exact bulkFusionBulkComponent11010 r z hr
  · exact bulkFusionBulkComponent11011 r z
  · exact bulkFusionBulkComponent11012 r z
  · exact bulkFusionBulkComponent11020 r z
  · exact bulkFusionBulkComponent11021 r z
  · exact bulkFusionBulkComponent11022 r z
  · exact bulkFusionBulkComponent11100 r z
  · exact bulkFusionBulkComponent11101 r z
  · exact bulkFusionBulkComponent11102 r z hr
  · exact bulkFusionBulkComponent11110 r z
  · exact bulkFusionBulkComponent11111 r z hr
  · exact bulkFusionBulkComponent11112 r z
  · exact bulkFusionBulkComponent11120 r z hr
  · exact bulkFusionBulkComponent11121 r z
  · exact bulkFusionBulkComponent11122 r z
  · exact bulkFusionBulkComponent11200 r z
  · exact bulkFusionBulkComponent11201 r z
  · exact bulkFusionBulkComponent11202 r z
  · exact bulkFusionBulkComponent11210 r z
  · exact bulkFusionBulkComponent11211 r z
  · exact bulkFusionBulkComponent11212 r z hr
  · exact bulkFusionBulkComponent11220 r z
  · exact bulkFusionBulkComponent11221 r z hr
  · exact bulkFusionBulkComponent11222 r z
  · exact bulkFusionBulkComponent12000 r z
  · exact bulkFusionBulkComponent12001 r z
  · exact bulkFusionBulkComponent12002 r z hr
  · exact bulkFusionBulkComponent12010 r z
  · exact bulkFusionBulkComponent12011 r z hr
  · exact bulkFusionBulkComponent12012 r z
  · exact bulkFusionBulkComponent12020 r z hr
  · exact bulkFusionBulkComponent12021 r z
  · exact bulkFusionBulkComponent12022 r z
  · exact bulkFusionBulkComponent12100 r z
  · exact bulkFusionBulkComponent12101 r z
  · exact bulkFusionBulkComponent12102 r z
  · exact bulkFusionBulkComponent12110 r z
  · exact bulkFusionBulkComponent12111 r z
  · exact bulkFusionBulkComponent12112 r z hr
  · exact bulkFusionBulkComponent12120 r z
  · exact bulkFusionBulkComponent12121 r z hr
  · exact bulkFusionBulkComponent12122 r z
  · exact bulkFusionBulkComponent12200 r z
  · exact bulkFusionBulkComponent12201 r z
  · exact bulkFusionBulkComponent12202 r z
  · exact bulkFusionBulkComponent12210 r z
  · exact bulkFusionBulkComponent12211 r z
  · exact bulkFusionBulkComponent12212 r z
  · exact bulkFusionBulkComponent12220 r z
  · exact bulkFusionBulkComponent12221 r z
  · exact bulkFusionBulkComponent12222 r z hr
  · exact bulkFusionBulkComponent20000 r z
  · exact bulkFusionBulkComponent20001 r z hr
  · exact bulkFusionBulkComponent20002 r z
  · exact bulkFusionBulkComponent20010 r z hr
  · exact bulkFusionBulkComponent20011 r z
  · exact bulkFusionBulkComponent20012 r z
  · exact bulkFusionBulkComponent20020 r z
  · exact bulkFusionBulkComponent20021 r z
  · exact bulkFusionBulkComponent20022 r z
  · exact bulkFusionBulkComponent20100 r z
  · exact bulkFusionBulkComponent20101 r z
  · exact bulkFusionBulkComponent20102 r z hr
  · exact bulkFusionBulkComponent20110 r z
  · exact bulkFusionBulkComponent20111 r z hr
  · exact bulkFusionBulkComponent20112 r z
  · exact bulkFusionBulkComponent20120 r z hr
  · exact bulkFusionBulkComponent20121 r z
  · exact bulkFusionBulkComponent20122 r z
  · exact bulkFusionBulkComponent20200 r z
  · exact bulkFusionBulkComponent20201 r z
  · exact bulkFusionBulkComponent20202 r z
  · exact bulkFusionBulkComponent20210 r z
  · exact bulkFusionBulkComponent20211 r z
  · exact bulkFusionBulkComponent20212 r z hr
  · exact bulkFusionBulkComponent20220 r z
  · exact bulkFusionBulkComponent20221 r z hr
  · exact bulkFusionBulkComponent20222 r z
  · exact bulkFusionBulkComponent21000 r z
  · exact bulkFusionBulkComponent21001 r z
  · exact bulkFusionBulkComponent21002 r z hr
  · exact bulkFusionBulkComponent21010 r z
  · exact bulkFusionBulkComponent21011 r z hr
  · exact bulkFusionBulkComponent21012 r z
  · exact bulkFusionBulkComponent21020 r z hr
  · exact bulkFusionBulkComponent21021 r z
  · exact bulkFusionBulkComponent21022 r z
  · exact bulkFusionBulkComponent21100 r z
  · exact bulkFusionBulkComponent21101 r z
  · exact bulkFusionBulkComponent21102 r z
  · exact bulkFusionBulkComponent21110 r z
  · exact bulkFusionBulkComponent21111 r z
  · exact bulkFusionBulkComponent21112 r z hr
  · exact bulkFusionBulkComponent21120 r z
  · exact bulkFusionBulkComponent21121 r z hr
  · exact bulkFusionBulkComponent21122 r z
  · exact bulkFusionBulkComponent21200 r z
  · exact bulkFusionBulkComponent21201 r z
  · exact bulkFusionBulkComponent21202 r z
  · exact bulkFusionBulkComponent21210 r z
  · exact bulkFusionBulkComponent21211 r z
  · exact bulkFusionBulkComponent21212 r z
  · exact bulkFusionBulkComponent21220 r z
  · exact bulkFusionBulkComponent21221 r z
  · exact bulkFusionBulkComponent21222 r z hr
  · exact bulkFusionBulkComponent22000 r z
  · exact bulkFusionBulkComponent22001 r z
  · exact bulkFusionBulkComponent22002 r z
  · exact bulkFusionBulkComponent22010 r z
  · exact bulkFusionBulkComponent22011 r z
  · exact bulkFusionBulkComponent22012 r z hr
  · exact bulkFusionBulkComponent22020 r z
  · exact bulkFusionBulkComponent22021 r z hr
  · exact bulkFusionBulkComponent22022 r z
  · exact bulkFusionBulkComponent22100 r z
  · exact bulkFusionBulkComponent22101 r z
  · exact bulkFusionBulkComponent22102 r z
  · exact bulkFusionBulkComponent22110 r z
  · exact bulkFusionBulkComponent22111 r z
  · exact bulkFusionBulkComponent22112 r z
  · exact bulkFusionBulkComponent22120 r z
  · exact bulkFusionBulkComponent22121 r z
  · exact bulkFusionBulkComponent22122 r z hr
  · exact bulkFusionBulkComponent22200 r z
  · exact bulkFusionBulkComponent22201 r z
  · exact bulkFusionBulkComponent22202 r z
  · exact bulkFusionBulkComponent22210 r z
  · exact bulkFusionBulkComponent22211 r z
  · exact bulkFusionBulkComponent22212 r z
  · exact bulkFusionBulkComponent22220 r z
  · exact bulkFusionBulkComponent22221 r z
  · exact bulkFusionBulkComponent22222 r z
end
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

end OAI

import OAI.NumberTheory.TotientAsymptotic.FordFactorization
import OAI.NumberTheory.TotientAsymptotic.TupleTotients

namespace OAI

/-! Exact passage from Ford's canonical preimage coordinates to basic witnesses. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def fordRemainder (x : ℝ) (H n : ℕ) : RemainderDatum (L x H) :=
  ⟨fun i => fordPrime n (i.val+1),fordCofactor n (L x H+1)⟩

lemma fordRemainder_prime {x : ℝ} {H n i : ℕ} (hi : i ∈ Finset.Icc 1 (L x H)) :
    remainderPrime (fordRemainder x H n) i=fordPrime n i := by
  rw [remainderPrime,dite_eq_left (Finset.mem_Icc.mp hi)]
  change fordPrime n (i-1+1)=fordPrime n i
  congr 1
  have := (Finset.mem_Icc.mp hi).1
  omega

lemma fordRemainder_coord {x : ℝ} {H n i : ℕ} (hi : i ≤ L x H) :
    remainderCoord x (fordRemainder x H n) i=rawSimplexCoordinate x n i := by
  by_cases h0 : i=0
  · simp [remainderCoord,rawSimplexCoordinate,h0]
  · simp only [remainderCoord,rawSimplexCoordinate,ite_eq_right h0,primeDoubleLog]
    rw [fordRemainder_prime (Finset.mem_Icc.mpr ⟨by omega,hi⟩)]

lemma fordRemainder_basic {x : ℝ} {H n : ℕ} (hL : 0 < L x H)
    (hstruct : extractedStructureCondition x (P H) n)
    (hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H))) :
    IsBasicRemainder x H (fordRemainder x H n) := by
  have hlast : 0 < primeDoubleLog n (L x H) := lt_trans (by norm_num) hstruct.2.1
  have hindex := fordPrime_index_of_doubleLog_pos hlast
  refine ⟨fordCofactor_pos _ _,?_,?_,?_,hsize⟩
  · intro i hi
    rw [fordRemainder_prime hi,fordRemainder_coord (Finset.mem_Icc.mp hi).2]
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    rw [rawSimplexCoordinate,ite_eq_right hi0]
    exact ⟨fordPrime_prime (by have := (Finset.mem_Icc.mp hi).2; omega),hstruct.1 i hi⟩
  · intro i hi
    have hiL := (Finset.mem_Icc.mp hi).2
    rw [fordRemainder_coord hiL]
    by_cases he : i=L x H
    · subst i
      rw [ite_eq_left rfl]
      have hempty : Finset.Icc (L x H+1) (L x H)=∅ := by simp
      rw [hempty,Finset.sum_empty,one_mul]
      simpa only [rawSimplexCoordinate,ite_eq_right (Nat.ne_of_gt hL)] using hlast.le
    · rw [ite_eq_right he]
      convert hstruct.2.2 i (Finset.mem_Ico.mpr ⟨Nat.zero_le _,by unfold L at *; omega⟩) using 1
      apply Finset.sum_congr rfl
      intro r hr
      rw [fordRemainder_coord (Finset.mem_Icc.mp hr).2]
  · rw [fordRemainder_prime (Finset.mem_Icc.mpr ⟨hL,le_rfl⟩)]
    exact fordCofactor_largest hindex

lemma fordRemainder_factorization {x : ℝ} {H n : ℕ} (hn : 0 < n)
    (hindex : L x H < n.primeFactorsList.length) :
    wholePreimage (fordPrime n 0) (fordRemainder x H n)=n := by
  have he := ford_factorization hn (show L x H+1 ≤ n.primeFactorsList.length by omega)
  have hI : Finset.range (L x H+1)=insert 0 (Finset.Icc 1 (L x H)) := by
    ext i
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [hI,Finset.prod_insert (by simp)] at he
  rw [wholePreimage,suffixPreimage]
  have hp : (∏ i ∈ Finset.Icc (0+1) (L x H), remainderPrime (fordRemainder x H n) i)=
      ∏ i ∈ Finset.Icc 1 (L x H), fordPrime n i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact fordRemainder_prime hi
  rw [hp]
  change fordPrime n 0 * (fordCofactor n (L x H+1) * _) = n
  calc
    _ = fordCofactor n (L x H+1)*(fordPrime n 0*∏ i ∈ Finset.Icc 1 (L x H),fordPrime n i) := by ring
    _ = n := he.symm

end TotientAsymptotic

end

end OAI

import OAI.NumberTheory.TotientAsymptotic.StructuredRemainder
import OAI.NumberTheory.TotientAsymptotic.FullPrimeGrid

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def primeOnly {J : ℕ} (η : RemainderDatum J) : RemainderDatum J := ⟨η.primes,1⟩

def IsUntruncatedRemainder (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : Prop :=
  0 < η.cofactor ∧ IsBasicRemainder x H (primeOnly η) ∧
    largestPrimeFactor η.cofactor ≤ remainderPrime η (L x H)

lemma primeOnly_prime {J : ℕ} (η : RemainderDatum J) (i : ℕ) :
    remainderPrime (primeOnly η) i=remainderPrime η i := rfl

lemma primeOnly_coord {J : ℕ} (η : RemainderDatum J) (x : ℝ) (i : ℕ) :
    remainderCoord x (primeOnly η) i=remainderCoord x η i := rfl

lemma untruncated_basic {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsUntruncatedRemainder x H η)
    (hs : Real.log (η.cofactor : ℝ) ≤ Real.exp (2*bandScale x (L x H))) :
    IsBasicRemainder x H η :=
  ⟨hη.1,hη.2.1.2.1,hη.2.1.2.2.1,hη.2.2,hs⟩

lemma untruncated_prime_mem {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsUntruncatedRemainder x H η) : η.primes ∈ fullPrimeTuples x H := by
  exact Finset.mem_image.mpr ⟨primeOnly η,mem_basicRemainderFinset.mpr hη.2.1,rfl⟩

lemma fordRemainder_untruncated {x : ℝ} {H n : ℕ} (hL : 0 < L x H)
    (hstruct : extractedStructureCondition x (P H) n) :
    IsUntruncatedRemainder x H (fordRemainder x H n) := by
  have hlast : 0 < primeDoubleLog n (L x H) := lt_trans (by norm_num) hstruct.2.1
  have hindex := fordPrime_index_of_doubleLog_pos hlast
  refine ⟨fordCofactor_pos _ _,⟨by norm_num [primeOnly],?_,?_,?_,?_⟩,?_⟩
  · intro i hi
    change (remainderPrime (fordRemainder x H n) i).Prime ∧ _
    rw [fordRemainder_prime hi]
    have hcoord := fordRemainder_coord (n := n) (Finset.mem_Icc.mp hi).2
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    have hcoord' : remainderCoord x (primeOnly (fordRemainder x H n)) i=primeDoubleLog n i := by
      simpa only [primeOnly_coord,rawSimplexCoordinate,ite_eq_right hi0] using hcoord
    rw [hcoord']
    exact ⟨fordPrime_prime (by have := (Finset.mem_Icc.mp hi).2; omega),hstruct.1 i hi⟩
  · intro i hi
    have hiL := (Finset.mem_Icc.mp hi).2
    rw [primeOnly_coord,fordRemainder_coord hiL]
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
      rw [primeOnly_coord,fordRemainder_coord (Finset.mem_Icc.mp hr).2]
  · change largestPrimeFactor 1 ≤ remainderPrime (fordRemainder x H n) (L x H)
    rw [fordRemainder_prime (Finset.mem_Icc.mpr ⟨hL,le_rfl⟩)]
    simpa [largestPrimeFactor] using (fordPrime_prime hindex).one_lt.le
  · simpa only [primeOnly,Nat.cast_one,Real.log_one] using
      (Real.exp_pos (2*bandScale x (L x H))).le
  · change largestPrimeFactor (fordCofactor n (L x H+1)) ≤ _
    rw [fordRemainder_prime (Finset.mem_Icc.mpr ⟨hL,le_rfl⟩)]
    exact fordCofactor_largest hindex

end TotientAsymptotic

end

end OAI

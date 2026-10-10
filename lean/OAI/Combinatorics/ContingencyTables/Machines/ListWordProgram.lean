import OAI.Combinatorics.ContingencyTables.Transport.ListBitProposal
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

def getOptionFast : Realizer (fun x : List A×ℕ => x.1[x.2]?) :=
  (choose (composition (pair second (composition first listLength)) less)
    (composition (getDFast default) TreeTyped.some) (constant none)).congr (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq]
      by_cases h : x.2<x.1.length
      · rw [ite_eq_left h,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
        rfl
      · rw [ite_eq_right h,List.getElem?_eq_none (by omega)])

theorem polynomial_getOptionFast : PolynomialTime (getOptionFast (A := A)) := by
  unfold getOptionFast
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_listLength)) polynomial_less)
    (polynomial_composition (polynomial_getDFast default) polynomial_some)
    (polynomial_constant none))

def listWordChoice (x : List A×List Bool) : Option A :=
  x.1[StackAddition.value x.2]?

def listWordChoiceRealizer : Realizer (listWordChoice (A := A)) :=
  composition (pair first (composition second bitValue)) getOptionFast

theorem polynomial_listWordChoice : PolynomialTime (listWordChoiceRealizer (A := A)) :=
  polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_bitValue))
    polynomial_getOptionFast

omit [Codec A] [Inhabited A] in
lemma bitValue_eq_word (k : ℕ) (bits : Fin k → Bool) :
    StackAddition.value (List.ofFn bits)=(FairBits.binaryWordEquiv k bits).val := by
  have hv (k : ℕ) (bits : Fin k → Bool) :
      StackAddition.value (List.ofFn bits)=∑ i, (bits i).toNat*2^i.val := by
    induction k with
    | zero => simp [StackAddition.value]
    | succ k ih =>
      rw [List.ofFn_succ,StackAddition.value,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Nat.mul_one,Fin.val_succ,pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [hv]
  change _=∑ i : Fin k, (finTwoEquiv.symm (bits i)).val*2^i.val
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> rfl

omit [Codec A] [Inhabited A] in
theorem listWordChoice_ofFn (xs : List A) (k : ℕ) (bits : Fin k → Bool) :
    listWordChoice (xs,List.ofFn bits)=FairBits.listBitDraw xs k bits := by
  simp only [listWordChoice,FairBits.listBitDraw,bitValue_eq_word]

omit [Codec A] [Inhabited A] in
/-- The literal binary program has the previously proved dyadic proposal
law, including all unused indices that return `none`. -/
theorem listWordChoice_mass [Fintype A] [DecidableEq A]
    (xs : List A) (hxs : xs.Nodup) (k : ℕ) (hk : xs.length≤2^k) (a : A) :
    (FirstSuccess.mapLaw
      (FirstSuccess.uniformLaw (α := Fin k → Bool))
      (fun bits => listWordChoice (xs,List.ofFn bits))).mass (some a)=
        if a∈xs then 1/(2:ℚ)^k else 0 := by
  simp_rw [listWordChoice_ofFn]
  exact FairBits.listBitDraw_mass xs hxs k hk a

end ContingencyTables.ProfilePrograms

end OAI

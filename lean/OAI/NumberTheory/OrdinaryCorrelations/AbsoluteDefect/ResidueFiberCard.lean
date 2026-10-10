import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryRationalResonance

lemma residue_fiber_card (S : Finset ℕ) (P q a : ℕ) (hq : 0<q)
    (hP : ∀n∈S,n≤P) :
    (S.filter (fun n=>n%q=a%q)).card≤P/q+1 := by
  have hf := Finset.card_le_card_of_injOn (s := S.filter (fun n=>n%q=a%q))
    (t := Finset.range (P/q+1)) (fun n : ℕ=>n/q)
    (by
      intro n hn
      apply Finset.mem_range.mpr
      apply (Nat.div_lt_iff_lt_mul hq).mpr
      exact (hP n (mem_filter.mp hn).1).trans_lt
        ((Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (P/q))))
    (by
      intro n hn m hm hnm
      have hmod : n%q=m%q := (mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm
      change n/q=m/q at hnm
      calc
        n = n%q+q*(n/q) := (Nat.mod_add_div n q).symm
        _ = m%q+q*(m/q) := by rw [hmod,hnm]
        _ = m := Nat.mod_add_div m q)
  simpa using hf

def sameResiduePairs (S : Finset ℕ) (q : ℕ) : Finset (ℕ×ℕ) :=
  (S.product S).filter (fun z=>z.1%q=z.2%q)

lemma pair_count_fibers (S : Finset ℕ) (q : ℕ) :
    (sameResiduePairs S q).card =
      ∑n∈S,(S.filter (fun m=>m%q=n%q)).card := by
  simp only [sameResiduePairs,card_eq_sum_ones,sum_filter]
  refine (Finset.sum_product S S (fun a=>if a.1%q=a.2%q then (1:ℕ) else 0)).trans ?_
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro m hm
  simp only [eq_comm]

theorem same_residue_pair_count (S : Finset ℕ) (P q : ℕ) (hq : 0<q)
    (hP : ∀n∈S,n≤P) :
    (sameResiduePairs S q).card≤S.card*(P/q+1) := by
  rw [pair_count_fibers]
  calc
    _ ≤ ∑n∈S,(P/q+1) := sum_le_sum (fun n hn=>residue_fiber_card S P q n hq hP)
    _ = _ := by simp

lemma off_diagonal_residue_fiber (S : Finset ℕ) (P q a : ℕ) (hq : 0<q)
    (hP : ∀n∈S,n≤P) (ha : a∈S) :
    (S.filter (fun n=>n%q=a%q ∧ n≠a)).card≤P/q := by
  have hcard := residue_fiber_card S P q a hq hP
  have hmem : a∈S.filter (fun n=>n%q=a%q) := mem_filter.mpr ⟨ha,rfl⟩
  have herase := card_erase_add_one hmem
  have hid : S.filter (fun n=>n%q=a%q ∧ n≠a) =
      (S.filter (fun n=>n%q=a%q)).erase a := by
    ext n
    simp only [mem_filter,mem_erase]
    tauto
  rw [hid]
  omega

end OrdinaryRationalResonance

end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.SortedEncoding
import OAI.Computability.QuantumFactoring.ChildQueue

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open SortedWords

def naturalKids (xs : List ℕ) : List ℕ :=
  (xs.dedup.filter (fun a=>2<a)).map (·-1)

lemma naturalKids_cons (a : ℕ) (as : List ℕ) :
    naturalKids (a::as) = if 2<a ∧ a∉as then (a-1)::naturalKids as else naturalKids as := by
  by_cases hm : a∈as <;> by_cases ha : 2<a <;>
    simp [naturalKids,hm,ha]

lemma number_injective {w : ℕ} : Function.Injective (fun a : Basis w=>(bitsValue a).toNat) := by
  intro a b h
  exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)

lemma kids_numbers {w : ℕ} (hw : 2 ≤ w) (xs : List (Basis w)) :
    numbers (kids xs)=naturalKids (numbers xs) := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    have hm : (bitsValue a).toNat∈numbers as ↔ a∈as :=
      List.mem_map_of_injective number_injective
    simp only [numbers,List.map_cons] at ih ⊢
    rw [naturalKids_cons,kids]
    by_cases hc : 2<(bitsValue a).toNat ∧ a∉as
    · have hd : 2<(bitsValue a).toNat ∧ (bitsValue a).toNat∉numbers as := ⟨hc.1,fun h=>hc.2 (hm.mp h)⟩
      dsimp only [numbers] at hd
      rw [ite_eq_left hc,ite_eq_left hd,List.map_cons,predBits_value (by omega) a (by omega),ih]
    · have hd : ¬(2<(bitsValue a).toNat ∧ (bitsValue a).toNat∉numbers as) := by
        rintro ⟨h1,h2⟩
        exact hc ⟨h1,fun h=>h2 (hm.mpr h)⟩
      dsimp only [numbers] at hd
      rw [ite_eq_right hc,ite_eq_right hd,ih]

/-- No factorization oracle is used in the queue circuit: the child list obtained
from the ACTUAL correct sorted prime fields is the source's exact ordered child
list, with distinct primes within one node and occurrence multiplicity outside it. -/
lemma naturalKids_correct {N n : ℕ} {xs : List ℕ} (hN : 2 ≤ N)
    (hx : CorrectEncoding N n xs) : naturalKids xs=AuxiliaryTree.children N := by
  obtain ⟨ps,hp,hs,hprod,_,rfl⟩ := hx
  let ys := (ps++List.replicate (n-ps.length) 0).dedup.filter (fun a=>2<a)
  have hmem (p : ℕ) : p∈ys ↔ p.Prime ∧ p∣N ∧ 2<p := by
    have hperm := Nat.primeFactorsList_unique hprod hp
    dsimp only [ys]
    simp only [List.mem_filter,List.mem_dedup,decide_eq_true_eq,List.mem_append]
    constructor
    · rintro ⟨hm,ht⟩
      have hps : p∈ps := by
        rcases hm with hm | hm
        · exact hm
        · have hz := (List.mem_replicate.mp hm).2
          omega
      exact ⟨hp p hps,by rw [←hprod];exact List.dvd_prod hps,ht⟩
    · rintro ⟨hprime,hdvd,ht⟩
      exact ⟨Or.inl (hperm.mem_iff.mpr ((Nat.mem_primeFactorsList (by omega)).mpr ⟨hprime,hdvd⟩)),ht⟩
  have hn : ys.Nodup := (List.nodup_dedup _).filter _
  have hsorted : ys.Pairwise (·≤·) := by
    have hpad := paddedOrder_append ps (n-ps.length) hp hs
    have hsub : List.Sublist ys (ps++List.replicate (n-ps.length) 0) :=
      List.filter_sublist.trans (List.dedup_sublist _)
    apply (hpad.sublist hsub).imp_of_mem
    intro a b _ hb hab
    have hb2 := (hmem b).mp hb
    rcases hab with hb0 | hab
    · omega
    · exact hab.2
  have hfin : ys.toFinset=N.primeFactors.filter (fun p=>2<p) := by
    ext p
    simp only [List.mem_toFinset,hmem,Finset.mem_filter,
      Nat.mem_primeFactors_of_ne_zero (by omega : N≠0)]
    tauto
  have he : (N.primeFactors.filter (fun p=>2<p)).sort (·≤·)=ys := by
    rw [←hfin]
    exact (List.toFinset_sort (·≤·) hn).mpr hsorted
  change ys.map (·-1)=AuxiliaryTree.children N
  rw [AuxiliaryTree.children,he]

theorem kids_correct {w N n : ℕ} (hw : 2 ≤ w) (hN : 2 ≤ N)
    (xs : List (Basis w)) (hx : CorrectEncoding N n (numbers xs)) :
    numbers (kids xs)=AuxiliaryTree.children N := by
  rw [kids_numbers hw,naturalKids_correct hN hx]

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI

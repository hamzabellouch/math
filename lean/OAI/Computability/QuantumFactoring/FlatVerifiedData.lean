import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.DivisorData

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree
namespace PhysicalTree

/-- Data lookup runs on the retained flat rows, not on a factorization oracle. -/
def lookupFields (rows : List (ℕ×List ℕ)) (m : ℕ) : List ℕ :=
  match rows.find? (fun r=>decide (r.1=m)) with
  | none=>[]
  | some r=>r.2

def lookupPrimes (rows : List (ℕ×List ℕ)) (m : ℕ) : List ℕ :=
  (lookupFields rows m).filter (fun p=>decide (p≠0))

lemma lookupFields_correct {rows : List (ℕ×List ℕ)} {n N m : ℕ}
    (h : CompleteLog n N rows) (hm : m∈rows.map Prod.fst) (hpos : m≠0) :
    CorrectEncoding m n (lookupFields rows m) := by
  cases hf : rows.find? (fun r=>decide (r.1=m)) with
  | none=>
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
    have hh:=List.find?_eq_none.mp hf r hr
    simp only [he,decide_true] at hh
    contradiction
  | some r=>
    have hr:=List.mem_of_find?_eq_some hf
    have he : r.1=m := by simpa only [decide_eq_true_eq] using List.find?_some hf
    have hv:=h.2.1 r hr
    rcases hv with hz | hv
    · exact (hpos (he.symm.trans hz)).elim
    · simpa only [lookupFields,hf,he] using hv

lemma encoding_filter {n m : ℕ} {xs : List ℕ} (h : CorrectEncoding m n xs) :
    (∀ p∈xs.filter (fun p=>decide (p≠0)),p.Prime) ∧
      (xs.filter (fun p=>decide (p≠0))).prod=m := by
  obtain ⟨ps,hp,_hs,hprod,_hlen,rfl⟩:=h
  have he : (ps++List.replicate (n-ps.length) 0).filter (fun p=>decide (p≠0))=ps := by
    rw [List.filter_append]
    have hx : ps.filter (fun p=>decide (p≠0))=ps :=
      List.filter_eq_self.mpr (by intro p h; simpa only [decide_eq_true_eq] using (hp p h).ne_zero)
    rw [hx]
    simp
  rw [he]
  exact ⟨hp,hprod⟩

lemma lookupPrimes_correct {rows : List (ℕ×List ℕ)} {n N m : ℕ}
    (h : CompleteLog n N rows) (hm : m∈rows.map Prod.fst) (hpos : m≠0) :
    (∀ p∈lookupPrimes rows m,p.Prime) ∧ (lookupPrimes rows m).prod=m :=
  encoding_filter (lookupFields_correct h hm hpos)

def logDivisorPrimes (rows : List (ℕ×List ℕ)) (M m : ℕ) : List ℕ :=
  divisorPrimes m (lookupPrimes rows M)

lemma logDivisorPrimes_correct {rows : List (ℕ×List ℕ)} {n N M m : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0) (hd : m∣M) :
    (∀ p∈logDivisorPrimes rows M m,p.Prime) ∧ (logDivisorPrimes rows M m).prod=m := by
  obtain ⟨hp,hprod⟩:=lookupPrimes_correct h hM hpos
  exact ⟨divisorPrimes_prime m _ hp,divisorPrimes_prod _ hp (by rwa [hprod])⟩

lemma log_child_present {rows : List (ℕ×List ℕ)} {n N M d : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hd : d∈children M) :
    d∈rows.map Prod.fst := by
  obtain ⟨r,hr,he⟩:=List.mem_map.mp hM
  exact h.2.2 r hr d (by rwa [he])

/-- The only factor data used are supplied parent factors and already verified
p−1 rows. This representation is a mathematical list interface; its Boolean
implementation is a separate obligation, not hidden in this definition. -/
noncomputable def logTotientPrimes (rows : List (ℕ×List ℕ)) (M m : ℕ) : List ℕ :=
  let f:=primeRecord (logDivisorPrimes rows M m)
  (f.support.sort (·≤·)).flatMap (fun p=>
    List.replicate (f p-1) p ++ if p=2 then [] else lookupPrimes rows (p-1))

lemma logTotientPrimes_correct {rows : List (ℕ×List ℕ)} {n N M m : ℕ}
    (h : CompleteLog n N rows) (hM : M∈rows.map Prod.fst) (hpos : M≠0)
    (hm : 0 < m) (hd : m∣M) :
    (∀ p∈logTotientPrimes rows M m,p.Prime) ∧ (logTotientPrimes rows M m).prod=m.totient := by
  obtain ⟨hp,hprod⟩:=logDivisorPrimes_correct h hM hpos hd
  have hf : primeRecord (logDivisorPrimes rows M m)=m.factorization := by
    rw [primeRecord_eq_factorization _ hp,hprod]
  have hc (p : ℕ) (hp : p∈m.factorization.support) (h2 : p≠2) :
      (∀ q∈lookupPrimes rows (p-1),q.Prime) ∧ (lookupPrimes rows (p-1)).prod=p-1 := by
    have hpm:=Nat.mem_primeFactors.mp hp
    have hb : 2<p := by have := hpm.1.two_le; omega
    have hchild : p-1∈children M :=
      mem_children.mpr ⟨p,hpm.1,hpm.2.1.trans hd,hpos,hb,rfl⟩
    exact lookupPrimes_correct h (log_child_present h hM hchild) (by omega)
  rw [logTotientPrimes,hf]
  refine ⟨?_,?_⟩
  · intro p hp
    obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
    have hq':=(Finset.mem_sort (·≤·)).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · have he:=(List.mem_replicate.mp hp).2
      subst p
      exact Nat.prime_of_mem_primeFactors hq'
    · split_ifs at hp with h2
      · simp at hp
      · exact (hc q hq' h2).1 p hp
  · rw [prod_flatMap]
    calc
      _ = ((m.factorization.support.sort (·≤·)).map
          (fun p=>p^(m.factorization p-1)*(p-1))).prod := by
        congr 1
        apply List.map_congr_left
        intro p hp
        rw [List.prod_append,List.prod_replicate]
        split_ifs with h2
        · subst p; simp
        · rw [(hc p ((Finset.mem_sort (·≤·)).mp hp) h2).2]
      _ = m.factorization.prod (fun p e=>p^(e-1)*(p-1)) := by
        rw [←List.prod_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset]
        rfl
      _ = m.totient := (Nat.totient_eq_prod_factorization hm.ne').symm

theorem verified_log_strip_order {n N m : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N)
    (hb : N < 2^n) (hm : 2 ≤ m) (hd : m∣N)
    (h : NodeMachine.Trace n (2*n^2))
    (hv : (machine n).verified (initialQueue n N) (2*n^2) h) (a : (ZMod m)ˣ) :
    stripOrderFactors a
      (logTotientPrimes ((machine n).dataLog (initialQueue n N) (2*n^2) h) N m)
      m.totient=orderOf a := by
  have hc:=verified_complete_log hn hN hb h hv
  obtain ⟨hp,hprod⟩:=logTotientPrimes_correct hc hc.1 (by omega) (by omega) hd
  exact strip_totient_factors hm a _ hp hprod
end PhysicalTree
end ExactQuantumFactoring


end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.AKSNetworks

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

lemma twoadic_lt_width {d n : ℕ} (hd : d≠0) (hb : d<2^n) : padicValNat 2 d<n := by
  apply (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hd)
    ((padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) hd).mpr le_rfl)).trans_lt hb

lemma twoadic_eq_iff {a b n : ℕ} (ha : a≠0) (hb : b≠0) (haB : a<2^n) (hbB : b<2^n) :
    padicValNat 2 a=padicValNat 2 b ↔ ∀ i : Fin n,2^i.val∣a ↔ 2^i.val∣b := by
  simp only [padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) ha,
    padicValNat_dvd_iff_le_of_ne_one (by decide : 2≠1) hb]
  constructor
  · intro he i; rw [he]
  · intro h
    exact le_antisymm ((h ⟨_,twoadic_lt_width ha haB⟩).mp le_rfl)
      ((h ⟨_,twoadic_lt_width hb hbB⟩).mpr le_rfl)

namespace BitArithmetic

def bequiv {k : ℕ} (a b : BooleanNetwork k 1) : BooleanNetwork k 1 := (a.bxor b).bnot
lemma bequiv_value {k : ℕ} (a b : BooleanNetwork k 1) (x : Basis k) :
    (bequiv a b).eval x 0=true ↔ (a.eval x 0=true ↔ b.eval x 0=true) := by
  rw [bequiv,bnot_value,eval_bxor]
  cases a.eval x 0 <;> cases b.eval x 0 <;> decide
lemma bequiv_count {k : ℕ} (a b : BooleanNetwork k 1) :
    (bequiv a b).net.count=2*a.net.count+2*b.net.count+9 := by
  simp only [bequiv,count_bnot,count_bxor]

/-- Equality of exact dyadic valuations by bounded divisibility tests.  The
parameter is the word width, not an input-dependent search cap. -/
def sameTwoVal {k n : ℕ} (a b : BooleanNetwork k n) : BooleanNetwork k 1 :=
  all (List.ofFn (fun i : Fin n=>bequiv (a.comp (dividesNet n (2^i.val)))
    (b.comp (dividesNet n (2^i.val)))))

lemma sameTwoVal_value {k n : ℕ} (a b : BooleanNetwork k n) (x : Basis k)
    (ha : (bitsValue (a.eval x)).toNat≠0) (hb : (bitsValue (b.eval x)).toNat≠0) :
    (sameTwoVal a b).eval x 0=true ↔
      padicValNat 2 (bitsValue (a.eval x)).toNat=padicValNat 2 (bitsValue (b.eval x)).toNat := by
  rw [twoadic_eq_iff ha hb (bitsValue (a.eval x)).isLt (bitsValue (b.eval x)).isLt]
  simp only [sameTwoVal,all_eval,List.forall_mem_ofFn_iff,bequiv_value,eval_comp,
    dividesNet_value _ _ _ (Nat.pow_lt_pow_right (by decide : 1<2) (Fin.isLt _))]

lemma sameTwoVal_count {k n : ℕ} (a b : BooleanNetwork k n) :
    (sameTwoVal a b).net.count≤n*(2*a.net.count+2*b.net.count+864*n*n+616*n+118)+1 := by
  have hh:=all_count (List.ofFn (fun i : Fin n=>bequiv (a.comp (dividesNet n (2^i.val)))
    (b.comp (dividesNet n (2^i.val)))) )
    (c:=2*a.net.count+2*b.net.count+864*n*n+616*n+117) (by
      intro c hc
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
      have hd:=dividesNet_count n (2^i.val)
      simp only [bequiv_count,count_comp]
      nlinarith)
  change (all _).net.count≤_
  simp only [List.length_ofFn] at hh
  have hr : 2*a.net.count+2*b.net.count+864*n*n+616*n+117+1=
      2*a.net.count+2*b.net.count+864*n*n+616*n+118 := by omega
  rwa [hr] at hh
end BitArithmetic
end ExactQuantumFactoring


end

end OAI

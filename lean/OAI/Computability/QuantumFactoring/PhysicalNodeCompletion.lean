import Mathlib
import OAI.Computability.QuantumFactoring.NodeProgress
import OAI.Computability.QuantumFactoring.PhysicalMachineMass

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic FactorController AuxiliaryTree OrderTrial
namespace PhysicalNode

lemma config_good {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (t : ℕ) (ht : t ≤ 2*n) (h : SplitMachine.Trace n t)
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h) :
    ∃ xs ys, (machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h=
      NodeStateCircuit.pack xs ys false ∧ Good n N (2*n-t) xs ys := by
  have hbw : N<2^(n+1) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have ha : (bitsValue (natBasis (n+1) N)).toNat=N := by
    rw [natBasis_value,Nat.mod_eq_of_lt hbw]
  induction t with
  | zero=>
    refine ⟨[natBasis (n+1) N],[],rfl,⟨?_,?_,?_,?_⟩⟩
    · intro a ha'
      have he : a=natBasis (n+1) N := List.mem_singleton.mp ha'
      subst a
      rw [ha]
      exact ⟨hN,hb⟩
    · simp
    · simp only [values_cons,values_nil,List.prod_cons,List.prod_nil,ha,mul_one]
    · have hs := splitWeight_bound (by omega : 0<N) hb
      simp only [values_cons,values_nil,ha,weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
  | succ t ih=>
    obtain ⟨xs,ys,he,hg⟩ := ih (by omega) h.1 hp.1
    have hg' : Good n N ((2*n-(t+1))+1) xs ys := by
      convert hg using 1; omega
    have hpass : UniversalSplit.passed ((query n (2*n)).eval (NodeStateCircuit.pack xs ys false)) h.2 := by
      have hh := hp.2
      change UniversalSplit.passed ((query n (2*n)).eval ((machine n (2*n)).config _ t h.1)) h.2 at hh
      rw [he] at hh
      exact hh
    obtain ⟨xs',ys',he',hg'⟩ := next_good hn (by omega : 2*n-(t+1) ≤ 2*n) xs ys hg' h.2 hpass
    refine ⟨xs',ys',?_,hg'⟩
    change (machine n (2*n)).next ((machine n (2*n)).config _ t h.1) h.2=_
    rw [he,he']

/-- Every passing actual history of the literal 2n-clock machine ends in a
complete prime list, without sticky failure. The input and all next queries are
actual measured-word encodings, not an oracle call to mathematical factorization. -/
theorem complete {n N : ℕ} (hn : 128 ≤ n) (hN : 2 ≤ N) (hb : N<2^n)
    (h : SplitMachine.Trace n (2*n))
    (hp : (machine n (2*n)).passed (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h) :
    ∃ ys, (machine n (2*n)).config (NodeStateCircuit.pack [natBasis (n+1) N] [] false) (2*n) h=
      NodeStateCircuit.pack [] ys false ∧
      (∀ p ∈ values ys,p.Prime) ∧ (values ys).prod=N ∧ ys.length<n := by
  obtain ⟨xs,ys,he,hg⟩ := config_good hn hN hb (2*n) (le_refl _) h hp
  have hl := hg.length_le
  have hxs : xs=[] := List.length_eq_zero_iff.mp (by omega)
  subst xs
  have hpr : ∀ p ∈ values ys,p.Prime := by
    intro p hp'
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp'
    exact hg.primes a ha
  have hprod : (values ys).prod=N := by simpa only [values_nil,List.prod_nil,one_mul] using hg.product
  have hlen : (values ys).length=splitWeight N := (Nat.primeFactorsList_unique hprod hpr).length_eq
  have hlen' : ys.length<n := by
    have hb' := splitWeight_bound (by omega : 0<N) hb
    rw [values,List.length_map] at hlen
    omega
  exact ⟨ys,he,hpr,hprod,hlen'⟩

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.NodeProgress
import OAI.Computability.QuantumFactoring.NodeStateFailure

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

lemma next_safe {n N s : ℕ} (hn : 128  ≤  n) (xs ys : List (Basis (n+1)))
    (b : Bool) (h : Good n N s xs ys) (r : FixedSplit.Raw n) :
    ∃ xs' ys' b', (machine n s).next (NodeStateCircuit.pack xs ys b) r=
      NodeStateCircuit.pack xs' ys' b' ∧ Good n N s xs' ys' := by
  cases xs with
  | nil=>exact ⟨[],ys,b,next_nil hn ys b r,h⟩
  | cons a xs=>
    have ha:=h.bounded a (by simp)
    have ht : ∀ x∈xs,2 ≤ (bitsValue x).toNat ∧ (bitsValue x).toNat < 2^n :=
      fun x hx=>h.bounded x (List.mem_cons_of_mem _ hx)
    have hcap : xs.length ≤ s := by have hh:=h.length_le; simp only [List.length_cons] at hh;omega
    by_cases hp : (bitsValue a).toNat.Prime
    · refine ⟨xs,a::ys,b,next_prime hn a xs ys b hcap hp r,⟨ht,?_,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp
        · exact h.primes z hz
      · have hh:=h.product
        simp only [values_cons,List.prod_cons] at hh ⊢
        calc
          (values xs).prod*((bitsValue a).toNat*(values ys).prod)=
            ((bitsValue a).toNat*(values xs).prod)*(values ys).prod := by ac_rfl
          _=N := hh
      · have hw:=h.clock
        rw [values_cons,weight_prime _ _ hp] at hw
        omega
    · let q:=(query n s).eval (NodeStateCircuit.pack (a::xs) ys b)
      let d:=decoded q r
      by_cases hd : ProperDivisor (bitsValue a).toNat (bitsValue d).toNat
      · let z:=(NodeCircuit.quotient s (n+1)).eval (NodeCircuit.pack (a::xs) d)
        have hz : (bitsValue z).toNat=(bitsValue a).toNat/(bitsValue d).toNat :=
          NodeCircuit.quotient_pack a d xs
        have hquot:=hd.quotient
        refine ⟨d::z::xs,ys,b,?_,⟨?_,h.primes,?_,?_⟩⟩
        · rw [next_eq]
          exact NodeStateCircuit.step_split (by omega) _ _ _ _ _ hcap ha.1 hp hd
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨by have hh:=hd.1;omega,hd.2.1.trans ha.2⟩
          · rcases List.mem_cons.mp hv with rfl | hv
            · rw [hz]
              exact ⟨hquot.1,hquot.2.1.trans ha.2⟩
            · exact ht v hv
        · have hh:=h.product
          simp only [values_cons,List.prod_cons] at hh ⊢
          rw [hz,←Nat.mul_assoc,hd.quotient.2.2]
          exact hh
        · have hw:=h.clock
          rw [values_cons,weight_split hd] at hw
          simpa only [values_cons,hz] using
            (show weight ((bitsValue d).toNat::(bitsValue a).toNat/(bitsValue d).toNat::values xs) ≤ s by omega)
      · refine ⟨a::xs,ys,true,?_,h⟩
        rw [next_eq]
        exact NodeStateCircuit.step_failure (by omega) a d xs ys b hcap ha.1 hp hd

/-- Safety is unconditional on every raw quantum outcome. In particular even a
failed retained candidate only stalls; all subsequent nonzero queries divide
this node's original modulus. -/
theorem config_safe {n N : ℕ} (hn : 128  ≤  n) (hN : 2  ≤  N) (hb : N < 2^n)
    (t : ℕ) (h : SplitMachine.Trace n t) :
    ∃ xs ys b, (machine n (2*n)).config
        (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h=NodeStateCircuit.pack xs ys b ∧
      Good n N (2*n) xs ys := by
  induction t with
  | zero=>
    have hbw : N < 2^(n+1) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have ha : (bitsValue (natBasis (n+1) N)).toNat=N := by
      rw [natBasis_value,Nat.mod_eq_of_lt hbw]
    refine ⟨[natBasis (n+1) N],[],false,rfl,⟨?_,?_,?_,?_⟩⟩
    · intro a ha'
      have he : a=natBasis (n+1) N := List.mem_singleton.mp ha'
      subst a
      rw [ha]
      exact ⟨hN,hb⟩
    · simp
    · simp only [values_cons,values_nil,List.prod_cons,List.prod_nil,ha,mul_one]
    · have hs:=splitWeight_bound (by omega : 0 < N) hb
      simp only [values_cons,values_nil,ha,weight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      omega
  | succ t ih=>
    obtain ⟨xs,ys,b,he,hg⟩:=ih h.1
    obtain ⟨xs',ys',b',he',hg'⟩:=next_safe hn xs ys b hg h.2
    refine ⟨xs',ys',b',?_,hg'⟩
    change (machine n (2*n)).next ((machine n (2*n)).config _ t h.1) h.2=_
    rw [he,he']

lemma Good.pending_dvd {n N s : ℕ} {xs ys : List (Basis (n+1))}
    (h : Good n N s xs ys) (a : Basis (n+1)) (ha : a∈xs) : (bitsValue a).toNat ∣ N := by
  rw [←h.product]
  exact (List.dvd_prod (List.mem_map.mpr ⟨a,ha,rfl⟩)).trans (dvd_mul_right _ _)

theorem query_safe {n N : ℕ} (hn : 128  ≤  n) (hN : 2  ≤  N) (hb : N < 2^n)
    (t : ℕ) (h : SplitMachine.Trace n t) :
    let m:=(bitsValue ((query n (2*n)).eval ((machine n (2*n)).config
      (NodeStateCircuit.pack [natBasis (n+1) N] [] false) t h))).toNat
    m=0 ∨ (2 ≤ m ∧ m < 2^n ∧ m ∣ N) := by
  obtain ⟨xs,ys,b,he,hg⟩:=config_safe hn hN hb t h
  dsimp only
  rw [he]
  cases xs with
  | nil=>
    left
    rw [query,eval_comp,NodeStateCircuit.top_pack]
    change (bitsValue ((resizeWord (n+1) n).eval (fun _=>false))).toNat=0
    rw [resizeWord_value,zeroBasis_value]
    simp
  | cons a xs=>
    have ha:=hg.bounded a (by simp)
    rw [query_value a xs ys b ha.2]
    exact Or.inr ⟨ha.1,ha.2,hg.pending_dvd a (by simp)⟩
end PhysicalNode
end ExactQuantumFactoring


end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.NodeSplitMachine
import OAI.Computability.QuantumFactoring.NodeStateNil

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic FactorController
namespace PhysicalNode

def values {w : ℕ} (xs : List (Basis w)) : List ℕ := xs.map (fun x=>(bitsValue x).toNat)
@[simp] lemma values_nil (w : ℕ) : values ([] : List (Basis w))=[] := rfl
@[simp] lemma values_cons {w : ℕ} (a : Basis w) (xs : List (Basis w)) :
    values (a::xs)=(bitsValue a).toNat::values xs := rfl

lemma length_le_weight (ms : List ℕ) (hm : ∀ m ∈ ms,2 ≤ m) : ms.length ≤ weight ms := by
  induction ms with
  | nil=>simp [weight]
  | cons m ms ih=>
    have hp := splitWeight_pos (hm m (by simp))
    have ht := ih (fun a ha=>hm a (by simp [ha]))
    simp only [List.length_cons,weight,List.map_cons,List.sum_cons] at *
    omega

structure Good (n N fuel : ℕ) (xs ys : List (Basis (n+1))) : Prop where
  bounded : ∀ a ∈ xs, 2 ≤ (bitsValue a).toNat ∧ (bitsValue a).toNat<2^n
  primes : ∀ a ∈ ys, (bitsValue a).toNat.Prime
  product : (values xs).prod*(values ys).prod=N
  clock : weight (values xs) ≤ fuel

lemma Good.length_le {n N f : ℕ} {xs ys : List (Basis (n+1))} (h : Good n N f xs ys) :
    xs.length ≤ f := by
  have hh := length_le_weight (values xs) (by
    intro m hm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact (h.bounded a ha).1)
  have hl : (values xs).length=xs.length := List.length_map _
  rw [hl] at hh
  exact hh.trans h.clock

lemma next_nil {n s : ℕ} (hn : 128 ≤ n) (ys : List (Basis (n+1))) (b : Bool) (r : FixedSplit.Raw n) :
    (machine n s).next (NodeStateCircuit.pack [] ys b) r=NodeStateCircuit.pack [] ys b := by
  rw [next_eq]
  exact NodeStateCircuit.step_nil (by omega) _ _ _

/-- One literal machine step consumes one unit of the genuine prime-factor
weight whenever pending work is nonempty. Empty work stays empty. -/
theorem next_good {n N s k : ℕ} (hn : 128 ≤ n) (hk : k ≤ s)
    (xs ys : List (Basis (n+1))) (h : Good n N (k+1) xs ys) (r : FixedSplit.Raw n)
    (hr : UniversalSplit.passed ((query n s).eval (NodeStateCircuit.pack xs ys false)) r) :
    ∃ xs' ys', (machine n s).next (NodeStateCircuit.pack xs ys false) r=
      NodeStateCircuit.pack xs' ys' false ∧ Good n N k xs' ys' := by
  cases xs with
  | nil=>
    refine ⟨[],ys,next_nil hn ys false r,⟨h.bounded,h.primes,h.product,?_⟩⟩
    simp [weight]
  | cons a xs=>
    have ha := h.bounded a (by simp)
    have ht : ∀ x ∈ xs,2 ≤ (bitsValue x).toNat ∧ (bitsValue x).toNat<2^n :=
      fun x hx=>h.bounded x (by simp [hx])
    have hcap : xs.length ≤ s := by have hh:=h.length_le; simp only [List.length_cons] at hh;omega
    by_cases hp : (bitsValue a).toNat.Prime
    · refine ⟨xs,a::ys,next_prime hn a xs ys false hcap hp r,⟨ht,?_,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp
        · exact h.primes z hz
      · have he := h.product
        simp only [values_cons,List.prod_cons] at he ⊢
        calc
          (values xs).prod*((bitsValue a).toNat*(values ys).prod)=
            ((bitsValue a).toNat*(values xs).prod)*(values ys).prod := by ac_rfl
          _=N := he
      · have hw := h.clock
        rw [values_cons,weight_prime _ _ hp] at hw
        omega
    · let q := (query n s).eval (NodeStateCircuit.pack (a::xs) ys false)
      let d := decoded q r
      let b := (NodeCircuit.quotient s (n+1)).eval (NodeCircuit.pack (a::xs) d)
      obtain ⟨he,hd⟩ := next_split hn a xs ys false hcap ha.1 ha.2 hp r hr
      change (machine n s).next (NodeStateCircuit.pack (a::xs) ys false) r=
        NodeStateCircuit.pack (d::b::xs) ys false at he
      change ProperDivisor (bitsValue a).toNat (bitsValue d).toNat at hd
      have hb : (bitsValue b).toNat=(bitsValue a).toNat/(bitsValue d).toNat :=
        NodeCircuit.quotient_pack a d xs
      have hquot := hd.quotient
      refine ⟨d::b::xs,ys,he,⟨?_,h.primes,?_,?_⟩⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨by have hh:=hd.1;omega,hd.2.1.trans ha.2⟩
        · rcases List.mem_cons.mp hz with rfl | hz
          · rw [hb]
            exact ⟨hquot.1,hquot.2.1.trans ha.2⟩
          · exact ht z hz
      · have hh := h.product
        simp only [values_cons,List.prod_cons] at hh ⊢
        rw [hb,←Nat.mul_assoc,hd.quotient.2.2]
        exact hh
      · have hw := h.clock
        rw [values_cons,weight_split hd] at hw
        simpa only [values_cons,hb] using (show weight
          ((bitsValue d).toNat::(bitsValue a).toNat/(bitsValue d).toNat::values xs) ≤ k by omega)

end PhysicalNode
end ExactQuantumFactoring


end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.NodeControlCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController
namespace NodeStateCircuit

abbrev width (s w : ℕ) := ((s+1)*w+(s+1)*w)+1
abbrev inWidth (s w : ℕ) := width s w+w

def pending (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  select ((Fin.castAdd 1) ∘ (Fin.castAdd ((s+1)*w)))
def output (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  select ((Fin.castAdd 1) ∘ (Fin.natAdd ((s+1)*w)))
def bad (s w : ℕ) : BooleanNetwork (width s w) 1 :=
  select (Fin.natAdd ((s+1)*w+(s+1)*w))
def top (s w : ℕ) : BooleanNetwork (width s w) w := (pending s w).comp (blockNet (s+1) w 0)
def old (s w : ℕ) : BooleanNetwork (inWidth s w) (width s w) := select (Fin.castAdd w)
def supplied (s w : ℕ) : BooleanNetwork (inWidth s w) w := select (Fin.natAdd (width s w))
def nodeInput (s w : ℕ) : BooleanNetwork (inWidth s w) (NodeCircuit.width s w) :=
  ((old s w).comp (pending s w)).pair (supplied s w)
def nextPending (s w : ℕ) : BooleanNetwork (inWidth s w) ((s+1)*w) :=
  (nodeInput s w).comp (NodeCircuit.next s w)
def emission (s w : ℕ) : BooleanNetwork (inWidth s w) w :=
  (nodeInput s w).comp (NodeCircuit.emitted s w)
def nextOutput (s w : ℕ) : BooleanNetwork (inWidth s w) ((s+1)*w) :=
  wordMux (zeroWord (emission s w)) ((old s w).comp (output s w))
    (stackPush (emission s w) ((old s w).comp (output s w)))
def nextBad (s w : ℕ) : BooleanNetwork (inWidth s w) 1 :=
  ((old s w).comp (bad s w)).bor ((nodeInput s w).comp (NodeCircuit.failed s w))
def step (s w : ℕ) : BooleanNetwork (inWidth s w) (width s w) :=
  ((nextPending s w).pair (nextOutput s w)).pair (nextBad s w)

def pack {s w : ℕ} (xs ys : List (Basis w)) (bad : Bool) : Basis (width s w) :=
  Fin.append (Fin.append (stackEncoding (s+1) w xs) (stackEncoding (s+1) w ys)) (fun _=>bad)

@[simp] lemma pending_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (pending s w).eval (pack xs ys b)=stackEncoding (s+1) w xs := by
  funext i
  simp [pending,eval_select,pack]
@[simp] lemma output_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (output s w).eval (pack xs ys b)=stackEncoding (s+1) w ys := by
  funext i
  rw [output,eval_select]
  change Fin.append (Fin.append (stackEncoding (s+1) w xs) (stackEncoding (s+1) w ys))
    (fun _=>b) (Fin.castAdd 1 (Fin.natAdd ((s+1)*w) i))=_
  rw [Fin.append_left,Fin.append_right]
@[simp] lemma bad_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (bad s w).eval (pack xs ys b)=(fun _=>b) := by
  funext i
  simp [bad,eval_select,pack]
lemma top_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (top s w).eval (pack xs ys b)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

lemma old_append {s w : ℕ} (x : Basis (width s w)) (d : Basis w) :
    (old s w).eval (Fin.append x d)=x := by
  funext i
  exact Fin.append_left _ _ i
lemma supplied_append {s w : ℕ} (x : Basis (width s w)) (d : Basis w) :
    (supplied s w).eval (Fin.append x d)=d := by
  funext i
  exact Fin.append_right _ _ i
lemma nodeInput_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) (d : Basis w) :
    (nodeInput s w).eval (Fin.append (pack xs ys b) d)=NodeCircuit.pack xs d := by
  rw [nodeInput,eval_pair,eval_comp,old_append,pending_pack,supplied_append]
  rfl

lemma nextBad_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) (d : Basis w)
    (hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack xs d) 0=false) :
    (nextBad s w).eval (Fin.append (pack xs ys b) d)=(fun _=>b) := by
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  rw [nextBad,eval_bor,eval_comp,old_append,bad_pack,eval_comp,nodeInput_pack,hf,Bool.or_false]

lemma step_prime {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs ys : List (Basis w))
    (b : Bool) (hx : xs.length ≤ s) (hp : (bitsValue a).toNat.Prime) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=pack xs (a::ys) b := by
  have ha : 2 ≤ (bitsValue a).toNat := hp.two_le
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=a := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_left hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0 ≠ true := by
    intro hz
    have hh := (zeroWord_value (emission s w) _).mp hz
    rw [he] at hh
    omega
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ((NodeCircuit.failed_pack_cons hw a d xs ha).mp hh).1 hp
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_left hp,nextOutput,wordMux_eval,ite_eq_right hz,
    stackPush_encoding _ _ _ ys (by rw [eval_comp,old_append,output_pack]),he,
    nextBad_pack _ _ _ _ hf]
  rfl

lemma step_split {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs ys : List (Basis w))
    (b : Bool) (hx : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) (hp : ¬(bitsValue a).toNat.Prime)
    (hd : ProperDivisor (bitsValue a).toNat (bitsValue d).toNat) :
    (step s w).eval (Fin.append (pack (a::xs) ys b) d)=
      pack (d::(NodeCircuit.quotient s w).eval (NodeCircuit.pack (a::xs) d)::xs) ys b := by
  have he : (emission s w).eval (Fin.append (pack (a::xs) ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_pack_cons hw,ite_eq_right hp]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack (a::xs) ys b) d) 0=true := by
    rw [zeroWord_value,he]
    have hh : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [bitsValue_bit _ ⟨i,hi⟩]
      simp
    rw [hh]
    rfl
  have hf : (NodeCircuit.failed s w).eval (NodeCircuit.pack (a::xs) d) 0=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    exact ((NodeCircuit.failed_pack_cons hw a d xs ha).mp hh).2 hd
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_pack_cons hw _ _ _ hx ha,ite_eq_right hp,ite_eq_left hd,nextOutput,wordMux_eval,ite_eq_left hz,
    eval_comp,old_append,output_pack,nextBad_pack _ _ _ _ hf]
  rfl

end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalNodeOutput
import OAI.Computability.QuantumFactoring.PhysicalNodeKernel
import OAI.Computability.QuantumFactoring.ChildQueueCorrect

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree
abbrev capacity (n : ℕ) := 2*n^2+1
abbrev configWidth (n : ℕ) := capacity n*n

def query (n : ℕ) : BooleanNetwork (configWidth n) n := blockNet (capacity n) n 0

def nodeResult (n : ℕ) : BooleanNetwork (NodeKernel.width n) (tensorWidth n n) :=
  ((PhysicalNode.machine n (2*n)).currentNet (2*n)).comp (PhysicalNode.sortedOutput n)
def fields (n : ℕ) : List (BooleanNetwork (NodeKernel.width n) n) :=
  List.ofFn (fun i : Fin n=>(nodeResult n).comp (tensorSelect n n i))

def old (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  select (Fin.castAdd (NodeKernel.width n))
def localNode (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (NodeKernel.width n) :=
  select (Fin.natAdd (configWidth n))
def pushed (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  (((localNode n).pair ((old n).comp (stackPop (capacity n) n))).comp
    (ChildQueue.pushAll (capacity n) (fields n))).comp
      (ChildQueue.queue (NodeKernel.width n) (capacity n) n)
/-- Literal fixed-capacity pending-node controller. The current modulus is
removed and this very node's distinct p−1 children are prepended in sorted order.
An empty queue is an idle tick, not a new root query. -/
def update (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  wordMux (zeroWord ((old n).comp (query n))) (old n) (pushed n)

lemma query_encoding (n : ℕ) (a : Basis n) (xs : List (Basis n)) :
    (query n).eval (stackEncoding (capacity n) n (a::xs))=a := by
  rw [query,blockNet_eval,block_stackEncoding]
  rfl
lemma old_append (n : ℕ) (x : Basis (configWidth n)) (y : Basis (NodeKernel.width n)) :
    (old n).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left _ _ i
lemma localNode_append (n : ℕ) (x : Basis (configWidth n)) (y : Basis (NodeKernel.width n)) :
    (localNode n).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right _ _ i

lemma fields_eval {n : ℕ} (z : Basis (NodeKernel.width n)) (xs : List (Basis n))
    (hlen : xs.length=n) (he : (nodeResult n).eval z=SortedWords.layout n n xs) :
    (fields n).map (fun a=>a.eval z)=xs := by
  have hpad := SortedWords.ofFn_getD_pad xs (fun _=>false) n hlen.le
  simp only [hlen,Nat.sub_self,List.replicate_zero,List.append_nil] at hpad
  have hl : SortedWords.layout n n xs=tensorLayout n n
      (fun i : Fin n=>xs[i.val]?.getD (fun _=>false)) := by
    calc
      _ = SortedWords.layout n n (List.ofFn (fun i : Fin n=>xs[i.val]?.getD (fun _=>false))) :=
        congrArg (SortedWords.layout n n) hpad.symm
      _ = _ := SortedWords.layout_ofFn _ _ _
  simp only [fields,List.map_ofFn,Function.comp_def,eval_comp,he,hl,tensorSelect_eval]
  exact hpad

lemma pushed_eval {n : ℕ} (hn : 2 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (z : Basis (NodeKernel.width n)) :
    (pushed n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) z)=
      stackEncoding (capacity n) n
        (ChildQueue.kids ((fields n).map (fun b=>b.eval z))++as) := by
  rw [pushed,eval_comp,eval_comp,eval_pair,localNode_append,eval_comp,old_append,
    stackPop_encoding _ hlen,ChildQueue.pushAll_eval hn,ChildQueue.queue_eval]
  rfl

lemma update_eval {n : ℕ} (hn : 2 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat) (z : Basis (NodeKernel.width n)) :
    (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) z)=
      stackEncoding (capacity n) n
        (ChildQueue.kids ((fields n).map (fun b=>b.eval z))++as) := by
  have htest : (zeroWord ((old n).comp (query n))).eval
      (Fin.append (stackEncoding (capacity n) n (a::as)) z) 0≠true := by
    intro h
    rw [zeroWord_value,eval_comp,old_append,query_encoding] at h
    omega
  rw [update,wordMux_eval,ite_eq_right htest,pushed_eval hn a as hlen z]

lemma update_nil (n : ℕ) (z : Basis (NodeKernel.width n)) :
    (update n).eval (Fin.append (stackEncoding (capacity n) n []) z)=
      stackEncoding (capacity n) n [] := by
  have hq : (query n).eval (stackEncoding (capacity n) n [])=fun _=>false := by
    rw [query,blockNet_eval,block_stackEncoding]
    rfl
  have ht : (zeroWord ((old n).comp (query n))).eval
      (Fin.append (stackEncoding (capacity n) n []) z) 0=true := by
    rw [zeroWord_value,eval_comp,old_append,hq,zeroBasis_value]
    rfl
  rw [update,wordMux_eval,ite_eq_left ht,old_append]

/-- Passed physical local computation produces EXACT canonical children in the
physical outer queue. It does not use trueData to select or initialize a query. -/
theorem update_passed {n : ℕ} (hn : 128 ≤ n) (a : Basis n) (as : List (Basis n))
    (hlen : (a::as).length ≤ capacity n) (ha : 2 ≤ (bitsValue a).toNat)
    (r : NodeKernel.Raw n) (hp : NodeKernel.passed a r) :
    ∃ kids : List (Basis n), SortedWords.numbers kids=AuxiliaryTree.children (bitsValue a).toNat ∧
      (update n).eval (Fin.append (stackEncoding (capacity n) n (a::as)) (NodeKernel.encoding a r))=
        stackEncoding (capacity n) n (kids++as) := by
  have hp' : (PhysicalNode.machine n (2*n)).passed
      (NodeStateCircuit.pack [natBasis (n+1) (bitsValue a).toNat] [] false) (2*n) r := by
    simpa only [NodeKernel.passed,NodeKernel.start,PhysicalNode.startNet_eval] using hp
  obtain ⟨zs,hl,hc,he⟩ := PhysicalNode.complete_output hn ha (bitsValue a).isLt r hp'
  have hf : (fields n).map (fun b=>b.eval (NodeKernel.encoding a r))=zs := by
    apply fields_eval _ zs hl
    rw [nodeResult,eval_comp,NodeKernel.encoding,SplitMachine.current_encoded,
      NodeKernel.start,PhysicalNode.startNet_eval]
    exact he
  refine ⟨ChildQueue.kids zs,ChildQueue.kids_correct (by omega) ha zs hc,?_⟩
  rw [update_eval (by omega : 2 ≤ n) a as hlen ha,hf]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

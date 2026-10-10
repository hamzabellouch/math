import Mathlib
import OAI.Computability.QuantumFactoring.BooleanNetworkFurther

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
inductive Node where
  | constant (b : Bool)
  | copy (i : ℕ)
  | neg (i : ℕ)
  | conj (i j : ℕ)
  deriving DecidableEq, Inhabited

def Node.map (f : ℕ→ℕ) : Node→Node
  | .constant b=>.constant b
  | .copy i=>.copy (f i)
  | .neg i=>.neg (f i)
  | .conj i j=>.conj (f i) (f j)
def eraseNode {n : ℕ} : BoolNode n→Node
  | .constant b=>.constant b
  | .copy i=>.copy i.val
  | .neg i=>.neg i.val
  | .conj i j=>.conj i.val j.val
lemma eraseNode_map {n m : ℕ} (o : BoolNode n) (f : Fin n→Fin m) (g : ℕ→ℕ)
    (h : ∀i,(f i).val=g i.val) : eraseNode (o.map f)=(eraseNode o).map g := by
  cases o <;> simp only [BoolNode.map,eraseNode,Node.map,h]
def eraseNet {n k : ℕ} : BoolNet n k→List Node
  | .input=>[]
  | .add p o=>eraseNet p++[eraseNode o]
lemma eraseNet_length {n k : ℕ} (p : BoolNet n k) : (eraseNet p).length=p.count := by
  induction p with
  | input=>rfl
  | add p o ih=>simp only [eraseNet,List.length_append,List.length_singleton,BoolNet.count,ih]

def attachIndex {m k : ℕ} (ρ : Fin m→Fin k) (i : ℕ) : ℕ :=
  if h : i < m then (ρ ⟨i,h⟩).val else k+(i-m)
lemma attachIndex_input {m k : ℕ} (ρ : Fin m→Fin k) (i : Fin m) :
    attachIndex ρ i.val=(ρ i).val := dite_eq_left i.isLt
lemma attachIndex_work {m k : ℕ} (ρ : Fin m→Fin k) (i : ℕ) (h : m ≤ i) :
    attachIndex ρ i=k+(i-m) := dite_eq_right (by omega)
lemma attach_output {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m→Fin k) (b : BoolNet m l)
    (i : Fin l) : ((a.attach ρ b).2.2 i).val=attachIndex ρ i.val := by
  induction b with
  | input=>exact (attachIndex_input ρ i).symm
  | @add l b o ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [BoolNet.attach,Fin.snoc_last,Fin.val_last]
      rw [attachIndex_work ρ l b.input_le]
      have hw:=(a.attach ρ b).2.1.width_eq
      have hc:=BoolNet.attach_count a ρ b
      have hb:=b.width_eq
      rw [hc] at hw
      have ha:=a.width_eq
      omega
    · simp only [BoolNet.attach,Fin.snoc_castSucc,Fin.val_castSucc]
      exact ih j
lemma attach_erase {n k m l : ℕ} (a : BoolNet n k) (ρ : Fin m→Fin k) (b : BoolNet m l) :
    eraseNet (a.attach ρ b).2.1=eraseNet a++(eraseNet b).map (Node.map (attachIndex ρ)) := by
  induction b with
  | input=>simp only [BoolNet.attach,eraseNet,List.map_nil,List.append_nil]
  | add b o ih=>
    simp only [BoolNet.attach,eraseNet,List.map_append,List.map_singleton]
    rw [ih,List.append_assoc,eraseNode_map o _ _ (attach_output a ρ b)]

structure Data where
  inputs : ℕ
  nodes : List Node
  outputs : List ℕ
  deriving Inhabited

def erase {n m : ℕ} (a : BooleanNetwork n m) : Data:=
  ⟨n,eraseNet a.net,List.ofFn (fun i=>(a.output i).val)⟩
def attachRawIndex (width : ℕ) (ρ : List ℕ) (i : ℕ) : ℕ:=
  if i<ρ.length then (ρ.drop i).headD 0 else width+(i-ρ.length)
lemma attachRawIndex_ofFn {m k : ℕ} (ρ : Fin m→Fin k) :
    attachRawIndex k (List.ofFn (fun i=>(ρ i).val))=attachIndex ρ := by
  funext i
  unfold attachRawIndex attachIndex
  simp only [List.length_ofFn]
  split_ifs with h
  · rw [List.headD_eq_head?_getD,List.head?_drop]
    simp [h]
  · rfl

def comp (a b : Data) : Data:=
  let f:=attachRawIndex (a.inputs+a.nodes.length) a.outputs
  ⟨a.inputs,a.nodes++b.nodes.map (Node.map f),b.outputs.map f⟩
lemma erase_comp {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork m l) :
    erase (a.comp b)=comp (erase a) (erase b) := by
  have hw : n+(eraseNet a.net).length=a.width := by rw [eraseNet_length];exact a.net.width_eq.symm
  simp only [erase,BooleanNetwork.comp,comp,hw,attachRawIndex_ofFn,attach_erase]
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext i
  exact attach_output a.net a.output b.net (b.output i)

def select (n : ℕ) (xs : List ℕ) : Data:=⟨n,[],xs⟩
lemma erase_select {n m : ℕ} (f : Fin m→Fin n) :
    erase (BooleanNetwork.select f)=select n (List.ofFn (fun i=>(f i).val)) := rfl

def node (n : ℕ) (o : Node) : Data:=⟨n,[o],[n]⟩
lemma erase_node {n : ℕ} (o : BoolNode n) : erase (BooleanNetwork.node o)=node n (eraseNode o) := by
  simp [erase,BooleanNetwork.node,eraseNet,node,List.ofFn_succ]
end ExactQuantumFactoring.NetworkEmission

end


end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.BooleanOracle
import OAI.Computability.QuantumFactoring.NetworkEmissionModel
import OAI.Computability.QuantumFactoring.CircuitEmissionModel

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open NetworkEmission

def notOp (t : ℕ) : Op:=⟨plainGate .not,[t]⟩
def cnotOp (a t : ℕ) : Op:=⟨plainGate .cnot,[a,t]⟩
def toffoliOp (a b t : ℕ) : Op:=⟨plainGate .toffoli,[a,b,t]⟩
lemma erase_notAt {q : ℕ} (t : Fin q) : eraseOp (notAt t)=notOp t.val:=rfl
lemma erase_cnotAt {q : ℕ} (a t : Fin q) (h : a≠t) : eraseOp (cnotAt a t h)=cnotOp a.val t.val:=rfl
lemma erase_toffoliAt {q : ℕ} (a b t : Fin q) (h : a≠b) (ha : a≠t) (hb : b≠t) :
    eraseOp (toffoliAt a b t h ha hb)=toffoliOp a.val b.val t.val:=rfl

def nodeOps (t : ℕ) : Node→List Op
  | .constant false=>[]
  | .constant true=>[notOp t]
  | .copy a=>[cnotOp a t]
  | .neg a=>[cnotOp a t,notOp t]
  | .conj a b=>if a=b then [cnotOp a t] else [toffoliOp a b t]
lemma erase_node_compile {n q : ℕ} (h : n+1≤q) (o : BoolNode n) :
    (o.compileOp h).compile.map eraseOp=nodeOps n (eraseNode o):=by
  cases o with
  | constant b=>cases b <;> rfl
  | copy a=>rfl
  | neg a=>rfl
  | conj a b=>
    simp only [BoolNode.compileOp,BooleanOp.compile,eraseNode,nodeOps]
    simp only [Fin.ext_iff,Fin.val_castLE]
    split_ifs <;> rfl

def netOps (n : ℕ) (xs : List Node) : List Op:=
  (xs.mapIdx (fun i o=>nodeOps (n+i) o)).flatten
lemma netOps_append_one (n : ℕ) (xs : List Node) (o : Node) :
    netOps n (xs++[o])=netOps n xs++nodeOps (n+xs.length) o:=by
  simp [netOps]
lemma erase_net_compile {n k q : ℕ} (p : BoolNet n k) (h : k≤q) :
    (p.program h).compile.map eraseOp=netOps n (eraseNet p):=by
  induction p with
  | input=>rfl
  | @add k p o ih=>
    simp only [BoolNet.program,BooleanProgram.compile,List.flatMap_append,List.flatMap_singleton,
      List.map_append,eraseNet,netOps_append_one]
    rw [←BooleanProgram.compile,ih,erase_node_compile,eraseNet_length,←p.width_eq]

def copyOps (k : ℕ) (xs : List ℕ) : List Op:=xs.mapIdx (fun i a=>cnotOp a (k+i))
lemma erase_copyPrefix {k m : ℕ} (f : Fin m→Fin k) (t : ℕ) (h : t ≤ m) :
    (BooleanNetwork.copyPrefix f t h).compile.map eraseOp=
      copyOps k (List.ofFn (fun i : Fin t=>(f (i.castLE h)).val)):=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    simp only [BooleanNetwork.copyPrefix,BooleanProgram.compile,List.flatMap_append,
      List.flatMap_singleton,List.map_append]
    rw [←BooleanProgram.compile,ih]
    rw [List.ofFn_succ',List.concat_eq_append]
    simp only [copyOps,List.mapIdx_append_one,List.length_ofFn]
    rfl

def oracleOps (a : NetworkEmission.Data) : List Op:=
  let p:=netOps a.inputs a.nodes
  p++copyOps (a.inputs+a.nodes.length) a.outputs++p.reverse.map Op.reverse
lemma erase_oracle {n m : ℕ} (a : BooleanNetwork n m) :
    a.oracle.map eraseOp=oracleOps (NetworkEmission.erase a):=by
  simp only [BooleanNetwork.oracle,List.map_append,List.map_map,List.map_reverse]
  have hr : (eraseOp ∘ (Instruction.reverse : Instruction (a.width+m)→_))=Op.reverse ∘ eraseOp:=rfl
  rw [hr,←List.map_map,erase_net_compile,erase_copyPrefix]
  have hw:=a.net.width_eq
  simp only [oracleOps,NetworkEmission.erase,eraseNet_length,←hw,copyOps]
  simp only [Fin.castLE_rfl,List.map_reverse,id_eq]
end ExactQuantumFactoring.CircuitEmission

end



end OAI

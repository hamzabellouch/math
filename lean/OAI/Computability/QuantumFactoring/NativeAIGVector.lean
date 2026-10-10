import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGModel

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

def eraseVec {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) : List Ref :=
  List.ofFn (fun i : Fin w=>((v.get i.val i.isLt).gate,(v.get i.val i.isLt).invert))
@[simp] lemma eraseVec_length {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) :
    (eraseVec v).length=w := List.length_ofFn
@[simp] lemma eraseVec_get {n w k : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) (h : k<w) :
    ((eraseVec v).drop k).headD (0,false)=((v.get k h).gate,(v.get k h).invert) := by
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp [eraseVec,h]
@[simp] lemma eraseVec_cast {n w : ℕ} {g g' : AIG (Fin n)} (v : AIG.RefVec g w)
    (h : g.decls.size≤g'.decls.size) : eraseVec (v.cast h)=eraseVec v := rfl
@[simp] lemma eraseVec_empty {n : ℕ} (g : AIG (Fin n)) : eraseVec (AIG.RefVec.empty (aig:=g))=[] := rfl
@[simp] lemma eraseVec_push {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w) (a : AIG.Ref g) :
    eraseVec (v.push a)=eraseVec v++[(a.gate,a.invert)] := by
  rw [eraseVec,List.ofFn_succ_last]
  congr 1
  · congr 1;funext i
    dsimp only [Fin.val_castSucc]
    rw [AIG.RefVec.get_push_ref_lt _ _ _ i.isLt]
  · simp

@[simp] lemma refVec_get_gate {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w)
    (idx : ℕ) (h : idx<w) : (v.get idx h).gate=v.refs[idx].gate := by
  cases v;rfl
@[simp] lemma refVec_get_invert {n w : ℕ} {g : AIG (Fin n)} (v : AIG.RefVec g w)
    (idx : ℕ) (h : idx<w) : (v.get idx h).invert=v.refs[idx].invert := by
  cases v;rfl

def VecRel {n w : ℕ} (r : Graph×List Ref) (v : AIG.RefVecEntry (Fin n) w) : Prop :=
  Rel r.1 v.aig ∧ r.2=eraseVec v.vec

def declIsZero : Decl→Bool
  | .zero=>true
  | _=>false
def known (r : Graph) (a : Ref) : Bool:=declIsZero (r.decls[a.1]?.getD .zero)
def countKnown (r : Graph) (as : List Ref) : ℕ := (as.filter (known r)).length
lemma known_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (a : AIG.Ref g) :
    known r (a.gate,a.invert) = (match g.decls[a.gate]'a.hgate with | .false=>true | _=>false) := by
  unfold known
  rw [h.1]
  simp only [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem a.hgate,
    Option.map_some,Option.getD_some]
  cases g.decls[a.gate]'a.hgate <;> rfl
end ExactQuantumFactoring.NativeAIG

end



end OAI

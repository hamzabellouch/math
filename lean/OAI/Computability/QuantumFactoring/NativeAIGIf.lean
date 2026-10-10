import Mathlib
import OAI.Computability.QuantumFactoring.Emission
import OAI.Computability.QuantumFactoring.NativeAIGVector
import OAI.Computability.QuantumFactoring.NativeAIGBounds

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

def ifGate (r : Graph) (d a b : Ref) : Graph×Ref :=
  let s:=gate r d a
  let t:=gate s.1 (notRef d) b
  orGate t.1 s.2 t.2
lemma if_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.TernaryInput g) :
    EPRel (ifGate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkIfCached i) := by
  let si : AIG.BinaryInput g:=⟨i.discr,i.lhs⟩
  let s:=g.mkAndCached si
  have hs:=gate_rel h si
  change EPRel (gate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert)) s at hs
  let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) g si
  let ti : AIG.BinaryInput s.aig:=⟨(i.discr.cast hsub).not,i.rhs.cast hsub⟩
  let t:=s.aig.mkAndCached ti
  have ht : EPRel (gate (gate r (i.discr.gate,i.discr.invert) (i.lhs.gate,i.lhs.invert)).1
      (notRef (i.discr.gate,i.discr.invert)) (i.rhs.gate,i.rhs.invert)) t := by
    simpa only [si,s,ti,t,AIG.mkAndCached,AIG.Ref.not,AIG.Ref.flip,Bool.true_xor,AIG.Ref.cast,notRef] using gate_rel hs.1 ti
  let hlor:=AIG.LawfulOperator.le_size (f:=AIG.mkAndCached) s.aig ti
  have hh:=or_rel ht.1 (⟨s.ref.cast hlor,t.ref⟩ : AIG.BinaryInput t.aig)
  change EPRel (orGate _ (s.ref.gate,s.ref.invert) (t.ref.gate,t.ref.invert)) _ at hh
  rw [←hs.2,←ht.2] at hh
  exact hh
lemma ifGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (d a b : Ref)
    (hd : d.1≤B) (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+3) (ifGate r d a b).1 ∧ (ifGate r d a b).2.1≤B+3 := by
  have hs:=gate_bound h d a hd ha
  have ht:=gate_bound hs.1 (notRef d) b (hd.trans (by omega)) (hb.trans (by omega))
  exact orGate_bound ht.1 _ _ (hs.2.trans (by omega)) ht.2

def ifLoop : ℕ→Graph→Ref→List Ref→List Ref→ℕ→List Ref→Graph×List Ref
  | 0,r,_,_,_,_,out=>(r,out)
  | k+1,r,d,lhs,rhs,curr,out=>
    let s:=ifGate r d ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false))
    ifLoop k s.1 d lhs rhs (curr+1) (out++[s.2])
def ifVec (r : Graph) (d : Ref) (lhs rhs : List Ref) : Graph×List Ref :=
  ifLoop lhs.length r d lhs rhs 0 []
lemma ifLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (d : AIG.Ref g) (lhs rhs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w)
    (out : AIG.RefVec g curr) :
    VecRel (ifLoop (w-curr) r (d.gate,d.invert) (eraseVec lhs) (eraseVec rhs) curr (eraseVec out))
      (AIG.RefVec.ite.go g curr hc d lhs rhs out) := by
  rw [AIG.RefVec.ite.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,ifLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let i : AIG.TernaryInput g:=⟨d,lhs.get curr hi,rhs.get curr hi⟩
    let s:=g.mkIfCached i
    have hs:=if_rel hr i
    let hsub:=AIG.LawfulOperator.le_size (f:=AIG.mkIfCached) g i
    have hh:=ifLoop_rel hs.1 (d.cast hsub) (lhs.cast hsub) (rhs.cast hsub)
      (curr+1) (by omega) ((out.cast hsub).push s.ref)
    simp only [eraseVec_cast,eraseVec_push,AIG.Ref.cast] at hh
    rw [hs.2]
    exact hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,ifLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma ifVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.RefVec.IfInput g w) :
    VecRel (ifVec r (i.discr.gate,i.discr.invert) (eraseVec i.lhs) (eraseVec i.rhs))
      (AIG.RefVec.ite g i) := by
  cases i with
  | mk d lhs rhs=>
    simpa only [AIG.RefVec.ite,ifVec,eraseVec_length,Nat.sub_zero,
      AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty] using
      ifLoop_rel hr d lhs rhs 0 (Nat.zero_le _) (.emptyWithCapacity w)

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def ifP : Procedure (prodCode graphCode tripleCode) (prodCode graphCode refCode)
    (fun x=>ifGate x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let r:=first graphCode tripleCode
  let abc:=second graphCode tripleCode
  let d:=(first refCode keyCode).comp abc
  let bc:=(second refCode keyCode).comp abc
  let a:=(first refCode refCode).comp bc
  let b:=(second refCode refCode).comp bc
  let s:=gateP.comp (r.pair (d.pair a))
  let t:=gateP.comp (((first graphCode refCode).comp s).pair ((notRefP.comp d).pair b))
  exact (orP.comp (((first graphCode refCode).comp t).pair
    (((second graphCode refCode).comp s).pair ((second graphCode refCode).comp t)))).congrFun (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

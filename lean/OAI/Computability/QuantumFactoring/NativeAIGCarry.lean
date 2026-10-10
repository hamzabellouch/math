import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGNot

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def carryLoop : ℕ→Graph→List Ref→List Ref→ℕ→Ref→Graph×Ref
  | 0,r,_,_,_,cin=>(r,cin)
  | k+1,r,lhs,rhs,curr,cin=>
    let s:=fullCarry r ((lhs.drop curr).headD (0,false)) ((rhs.drop curr).headD (0,false)) cin
    carryLoop k s.1 lhs rhs (curr+1) s.2
def overflow (r : Graph) (lhs rhs : List Ref) (cin : Ref) : Graph×Ref :=
  carryLoop lhs.length r lhs rhs 0 cin
def ult (r : Graph) (lhs rhs : List Ref) : Graph×Ref:=
  let s:=overflow r lhs (notVec rhs) (0,true)
  (s.1,notRef s.2)
lemma carryLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (curr : ℕ) (cin : AIG.Ref g) :
    EPRel (carryLoop (w-curr) r (eraseVec lhs) (eraseVec rhs) curr (cin.gate,cin.invert))
      (mkOverflowBit.go g lhs rhs curr cin) := by
  rw [mkOverflowBit.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,carryLoop,eraseVec_get lhs hi,eraseVec_get rhs hi]
    let ii : FullAdderInput g:=⟨lhs.get curr hi,rhs.get curr hi,cin⟩
    let cc:=mkFullAdderCarry g ii
    have hh:=fullCarry_rel hr ii
    let hle:=AIG.LawfulOperator.le_size (f:=mkFullAdderCarry) g ii
    have ht:=carryLoop_rel hh.1 (lhs.cast hle) (rhs.cast hle) (curr+1) cc.ref
    simp only [eraseVec_cast] at ht
    rw [←hh.2] at ht
    exact ht
  · rw [dite_eq_right hi,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi),carryLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma overflow_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : OverflowInput g) :
    EPRel (overflow r (eraseVec i.vec.lhs) (eraseVec i.vec.rhs) (i.cin.gate,i.cin.invert))
      (mkOverflowBit g i) := by
  cases i with
  | mk w v c=>
    simpa only [overflow,eraseVec_length,Nat.sub_zero,mkOverflowBit] using carryLoop_rel hr v.lhs v.rhs 0 c
lemma ult_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    EPRel (ult r (eraseVec i.lhs) (eraseVec i.rhs)) (Std.Tactic.BVDecide.BVPred.mkUlt g i) := by
  let nt:=blastNot g i.rhs
  have hn:=notVec_rel hr i.rhs
  let hle:=AIG.LawfulVecOperator.le_size (f:=blastNot) g i.rhs
  let oi : OverflowInput nt.aig:=⟨w,⟨i.lhs.cast hle,nt.vec⟩,nt.aig.mkConstCached true⟩
  have hh:=overflow_rel hn.1 oi
  change EPRel (overflow r (eraseVec i.lhs) (eraseVec nt.vec) (0,true)) (mkOverflowBit nt.aig oi) at hh
  rw [←hn.2] at hh
  refine ⟨hh.1,?_⟩
  simpa only [notRef,Std.Tactic.BVDecide.BVPred.mkUlt,AIG.mkNotCached,AIG.Ref.not,AIG.Ref.flip,
    Bool.true_xor,ult] using congrArg notRef hh.2
end ExactQuantumFactoring.NativeAIG

end


end OAI

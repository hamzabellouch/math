import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGShift
import OAI.Computability.QuantumFactoring.NativeAIGIf
import OAI.Computability.QuantumFactoring.NativeAIGCarry
import OAI.Computability.QuantumFactoring.NativeAIGSub
import OAI.Computability.QuantumFactoring.NativeAIGExtend
import OAI.Computability.QuantumFactoring.NativeAIGZipFold

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide Std.Tactic.BVDecide.BVExpr.bitblast

def divStep (g : Graph) (lhs rhs : List Ref) (wn : ℕ) (q rem : List Ref) : Graph×(List Ref×List Ref):=
  let r':=shiftConcat rem ((lhs.drop (wn-1)).headD (0,false))
  let posQ:=shiftConcat q (0,false)
  let negQ:=shiftConcat q (0,true)
  let negR:=sub g r' rhs
  let discr:=ult negR.1 r' rhs
  let nextQ:=ifVec discr.1 discr.2 posQ negQ
  let nextR:=ifVec nextQ.1 discr.2 r' negR.2
  (nextR.1,nextQ.2,nextR.2)
def divLoop : ℕ→Graph→List Ref→List Ref→ℕ→List Ref→List Ref→Graph×(List Ref×List Ref)
  | 0,g,_,_,_,q,rem=>(g,q,rem)
  | k+1,g,lhs,rhs,wn,q,rem=>
    let s:=divStep g lhs rhs wn q rem
    divLoop k s.1 lhs rhs (wn-1) s.2.1 s.2.2
def divide (g : Graph) (lhs rhs : List Ref) : Graph×List Ref:=
  let zero:=List.replicate lhs.length (0,false)
  let d:=eqVec g rhs zero
  let out:=divLoop lhs.length d.1 lhs rhs lhs.length zero zero
  ifVec out.1 d.2 zero out.2.1

lemma divStep_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (wn wr : ℕ) (q rem : AIG.RefVec g w) :
    let sr:=divStep r (eraseVec lhs) (eraseVec rhs) wn (eraseVec q) (eraseVec rem)
    let sn:=blastUdiv.blastDivSubtractShift g lhs rhs wn wr q rem
    Rel sr.1 sn.aig ∧ sr.2.1=eraseVec sn.q ∧ sr.2.2=eraseVec sn.r := by
  let ri : blastUdiv.ShiftConcatInput g w:=⟨rem,lhs.getD (wn-1) (g.mkConstCached false)⟩
  let rs:=blastUdiv.blastShiftConcat g ri
  have hrs:=shiftConcat_rel hr rem ri.bit
  change VecRel (r,shiftConcat (eraseVec rem)
    ((lhs.getD (wn-1) (g.mkConstCached false)).gate,(lhs.getD (wn-1) (g.mkConstCached false)).invert)) rs at hrs
  rw [←eraseVec_getD] at hrs
  let h₁:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) g ri
  let qi : blastUdiv.ShiftConcatInput rs.aig w:=⟨q.cast h₁,rs.aig.mkConstCached false⟩
  let qs:=blastUdiv.blastShiftConcat rs.aig qi
  have hqs:=shiftConcat_rel hrs.1 qi.lhs qi.bit
  change VecRel (r,shiftConcat (eraseVec q) (0,false)) qs at hqs
  let h₂:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) rs.aig qi
  let ni : blastUdiv.ShiftConcatInput qs.aig w:=⟨(q.cast h₁).cast h₂,qs.aig.mkConstCached true⟩
  let ns:=blastUdiv.blastShiftConcat qs.aig ni
  have hns:=shiftConcat_rel hqs.1 ni.lhs ni.bit
  change VecRel (r,shiftConcat (eraseVec q) (0,true)) ns at hns
  let h₃:=AIG.LawfulVecOperator.le_size (f:=blastUdiv.blastShiftConcat) qs.aig ni
  let si : AIG.BinaryRefVec ns.aig w:=⟨(rs.vec.cast h₂).cast h₃,((rhs.cast h₁).cast h₂).cast h₃⟩
  let ss:=blastSub ns.aig si
  have hss:=sub_rel hns.1 si
  change VecRel (sub r (eraseVec rs.vec) (eraseVec rhs)) ss at hss
  rw [←hrs.2] at hss
  let h₄:=AIG.LawfulVecOperator.le_size (f:=blastSub) ns.aig si
  let ui : AIG.BinaryRefVec ss.aig w:=⟨((rs.vec.cast h₂).cast h₃).cast h₄,
    (((rhs.cast h₁).cast h₂).cast h₃).cast h₄⟩
  let us:=BVPred.mkUlt ss.aig ui
  have hus:=ult_rel hss.1 ui
  change EPRel (ult _ (eraseVec rs.vec) (eraseVec rhs)) us at hus
  rw [←hrs.2] at hus
  let h₅:=AIG.LawfulOperator.le_size (f:=BVPred.mkUlt) ss.aig ui
  let qi' : AIG.RefVec.IfInput us.aig w:=⟨us.ref,((qs.vec.cast h₃).cast h₄).cast h₅,
    (ns.vec.cast h₄).cast h₅⟩
  let qs':=AIG.RefVec.ite us.aig qi'
  have hqs':=ifVec_rel hus.1 qi'
  change VecRel (ifVec _ (us.ref.gate,us.ref.invert) (eraseVec qs.vec) (eraseVec ns.vec)) qs' at hqs'
  rw [←hus.2,←hqs.2,←hns.2] at hqs'
  let h₆:=AIG.LawfulVecOperator.le_size (f:=AIG.RefVec.ite) us.aig qi'
  let ri' : AIG.RefVec.IfInput qs'.aig w:=⟨us.ref.cast h₆,
    (((rs.vec.cast h₂).cast h₃).cast h₄ |>.cast h₅).cast h₆,(ss.vec.cast h₅).cast h₆⟩
  let rs':=AIG.RefVec.ite qs'.aig ri'
  have hrs':=ifVec_rel hqs'.1 ri'
  change VecRel (ifVec _ (us.ref.gate,us.ref.invert) (eraseVec rs.vec) (eraseVec ss.vec)) rs' at hrs'
  rw [←hus.2,←hrs.2,←hss.2] at hrs'
  exact ⟨hrs'.1,hqs'.2,hrs'.2⟩

lemma divLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (lhs rhs : AIG.RefVec g w) (k wn wr : ℕ) (q rem : AIG.RefVec g w) :
    let sr:=divLoop k r (eraseVec lhs) (eraseVec rhs) wn (eraseVec q) (eraseVec rem)
    let sn:=blastUdiv.go g k lhs rhs wn wr q rem
    Rel sr.1 sn.aig ∧ sr.2.1=eraseVec sn.q ∧ sr.2.2=eraseVec sn.r := by
  induction k generalizing r g wn wr with
  | zero=>exact ⟨hr,rfl,rfl⟩
  | succ k ih=>
    let ss:=blastUdiv.blastDivSubtractShift g lhs rhs wn wr q rem
    have hs:=divStep_rel hr lhs rhs wn wr q rem
    have ht:=ih hs.1 (lhs.cast ss.hle) (rhs.cast ss.hle) ss.wn ss.wr ss.q ss.r
    simp only [eraseVec_cast] at ht
    rw [←hs.2.1,←hs.2.2] at ht
    exact ht
lemma divide_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (i : AIG.BinaryRefVec g w) :
    VecRel (divide r (eraseVec i.lhs) (eraseVec i.rhs)) (blastUdiv g i) := by
  let zi:=blastConst g (0 : BitVec w)
  let ei : AIG.BinaryRefVec g w:=⟨i.rhs,zi⟩
  let es:=BVPred.mkEq g ei
  have hes:=eqVec_rel hr ei
  change EPRel (eqVec r (eraseVec i.rhs) (eraseVec zi)) es at hes
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hes
  let h₁:=AIG.LawfulOperator.le_size (f:=BVPred.mkEq) g ei
  let ds:=blastUdiv.go es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  have hds:=divLoop_rel hes.1 (i.lhs.cast h₁) (i.rhs.cast h₁) w w 0 (zi.cast h₁) (zi.cast h₁)
  simp only [eraseVec_cast] at hds
  rw [show eraseVec zi=List.replicate w (0,false) from const_zero g] at hds
  let h₂:=blastUdiv.go_le_size es.aig w (i.lhs.cast h₁) (i.rhs.cast h₁) w 0 (zi.cast h₁) (zi.cast h₁)
  let qi : AIG.RefVec.IfInput ds.aig w:=⟨es.ref.cast h₂,(zi.cast h₁).cast h₂,ds.q⟩
  have hq:=ifVec_rel hds.1 qi
  change VecRel (ifVec _ (es.ref.gate,es.ref.invert) (eraseVec zi) (eraseVec ds.q)) _ at hq
  rw [←hes.2,←hds.2.1,show eraseVec zi=List.replicate w (0,false) from const_zero g] at hq
  have hn : AIG.RefVec.ite ds.aig qi = blastUdiv g i := by rfl
  change VecRel _ (AIG.RefVec.ite ds.aig qi) at hq
  rw [hn] at hq
  simpa only [divide,eraseVec_length] using hq
end ExactQuantumFactoring.NativeAIG

end



end OAI

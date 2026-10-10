import Mathlib
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def shiftBit (xs : List Ref) (d i : ℕ) : Ref:=
  if i<d then (0,false) else (xs.drop (i-d)).headD (0,false)
def shiftLoop : ℕ→List Ref→ℕ→ℕ→List Ref→List Ref
  | 0,_,_,_,out=>out
  | k+1,xs,d,i,out=>shiftLoop k xs d (i+1) (out++[shiftBit xs d i])
def shift (xs : List Ref) (d : ℕ) : List Ref:=
  (List.range xs.length).map (shiftBit xs d)
lemma shiftLoop_value (k : ℕ) (xs : List Ref) (d i : ℕ) (out : List Ref) :
    shiftLoop k xs d i out=out++(List.range' i k).map (shiftBit xs d) := by
  induction k generalizing i out with
  | zero=>simp [shiftLoop]
  | succ k ih=>simp [shiftLoop,ih,List.range'_succ,List.append_assoc]
lemma shiftLoop_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (d curr : ℕ) (hc : curr ≤ w) (out : AIG.RefVec g curr) :
    VecRel (r,shiftLoop (w-curr) (eraseVec xs) d curr (eraseVec out))
      (blastShiftLeftConst.go g xs d curr hc out) := by
  rw [blastShiftLeftConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    rw [hd,shiftLoop]
    by_cases he : curr<d
    · rw [dite_eq_left he,shiftBit,ite_eq_left he]
      have hh:=shiftLoop_rel hr xs d (curr+1) (by omega) (out.push (g.mkConstCached false))
      simpa only [eraseVec_push,AIG.mkConstCached] using hh
    · rw [dite_eq_right he,shiftBit,ite_eq_right he,eraseVec_get xs (by omega)]
      simpa only [eraseVec_push] using
        shiftLoop_rel hr xs d (curr+1) (by omega) (out.push (xs.get (curr-d) (by omega)))
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [Nat.sub_self,shiftLoop]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma shift_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (d : ℕ) :
    VecRel (r,shift (eraseVec xs) d) (blastShiftLeftConst g ⟨xs,d⟩) := by
  simpa only [blastShiftLeftConst,shiftLoop_value,eraseVec_empty,List.nil_append,
    AIG.RefVec.emptyWithCapacity_eq,Nat.sub_zero,List.range_eq_range',shift,eraseVec_length] using
    shiftLoop_rel hr xs d 0 (Nat.zero_le _) (.emptyWithCapacity w)

lemma const_zero_go {n w : ℕ} (g : AIG (Fin n)) (curr : ℕ) (hc : curr ≤ w)
    (out : AIG.RefVec g curr) :
    eraseVec (blastConst.go g (0 : BitVec w) curr out hc)=
      eraseVec out++List.replicate (w-curr) (0,false) := by
  rw [blastConst.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi,const_zero_go,eraseVec_push]
    have hd : w-curr=(w-(curr+1))+1:=by omega
    simp only [AIG.mkConstCached]
    rw [hd,List.replicate_succ]
    simp [List.append_assoc]
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    simp
termination_by w-curr
lemma const_zero {n w : ℕ} (g : AIG (Fin n)) :
    eraseVec (blastConst g (0 : BitVec w))=List.replicate w (0,false) := by
  simpa only [blastConst,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,Nat.sub_zero]
    using const_zero_go g 0 (Nat.zero_le _) (.emptyWithCapacity w)

namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def shiftBitP : Procedure (prodCode unaryCode (prodCode (listCode refCode) Nat.bits)) refCode
    (fun x=>shiftBit x.2.1 x.2.2 x.1) := by
  let i:=unaryToBits.comp (first unaryCode (prodCode (listCode refCode) Nat.bits))
  let env:=second unaryCode (prodCode (listCode refCode) Nat.bits)
  let xs:=(first (listCode refCode) Nat.bits).comp env
  let d:=(second (listCode refCode) Nat.bits).comp env
  let idx:=binarySub.comp (i.pair d)
  let get:=(listGet refCode (0,false)).comp (idx.pair xs)
  exact (conditional (binaryLt.comp (i.pair d)) (Procedure.constant _ refCode (0,false)) get).congrFun (by
    intro x;unfold shiftBit;split <;> simp_all)
noncomputable def shiftP : Procedure (prodCode (listCode refCode) Nat.bits) (listCode refCode)
    (fun x=>shift x.1 x.2) :=
  (tabulate (f:=fun (x : List Ref×ℕ) i=>shiftBit x.1 x.2 i) (0,false) shiftBitP).comp
    (((listUnaryLength refCode (0,false)).comp (first (listCode refCode) Nat.bits)).pair (identity _))
end Emission
end ExactQuantumFactoring.NativeAIG

end

end OAI

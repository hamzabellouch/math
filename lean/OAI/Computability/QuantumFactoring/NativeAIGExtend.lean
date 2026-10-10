import Mathlib
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

lemma eraseVec_getD {n w : ℕ} {g : AIG (Fin n)} (xs : AIG.RefVec g w) (i : ℕ) :
    ((eraseVec xs).drop i).headD (0,false)=
    ((xs.getD i (g.mkConstCached false)).gate,(xs.getD i (g.mkConstCached false)).invert) := by
  by_cases hi : i<w
  · rw [AIG.RefVec.get_in_bound _ _ _ hi,eraseVec_get xs hi]
  · rw [AIG.RefVec.get_out_bound _ _ _ (by omega),List.drop_eq_nil_of_le (by rw [eraseVec_length];omega)]
    rfl
lemma eraseVec_append {n w v : ℕ} {g : AIG (Fin n)} (lhs : AIG.RefVec g w) (rhs : AIG.RefVec g v) :
    eraseVec (lhs.append rhs)=eraseVec lhs++eraseVec rhs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [eraseVec,List.getElem_ofFn]
    rw [AIG.RefVec.get_append,List.getElem_append]
    by_cases hh : i<w
    · simp only [List.length_ofFn,hh,dite_eq_left,List.getElem_ofFn]
    · simp [hh]

def extend (xs : List Ref) (w : ℕ) : List Ref:=
  (List.range w).map (fun i=>(xs.drop i).headD (0,false))
lemma extend_length (xs : List Ref) (w : ℕ) : (extend xs w).length=w:=by simp [extend]
lemma extend_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) {w : ℕ} (hw : w≤B) :
    RefsBound B (extend xs w) := by
  refine ⟨by simpa only [extend_length],?_⟩
  intro a ha
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
  exact h.get _
lemma extend_go_rel {n w v : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤v) (out : AIG.RefVec g curr) :
    VecRel (r,eraseVec out++(List.range' curr (v-curr)).map (fun i=>((eraseVec xs).drop i).headD (0,false)))
      (blastZeroExtend.go g w xs v curr hc out) := by
  rw [blastZeroExtend.go]
  by_cases hi : curr<v
  · rw [dite_eq_left hi]
    have hd : v-curr=(v-(curr+1))+1:=by omega
    rw [hd,List.range'_succ,List.map_cons]
    by_cases he : curr<w
    · rw [dite_eq_left he,eraseVec_get xs he]
      simpa only [eraseVec_push,List.append_assoc,List.singleton_append] using
        extend_go_rel hr xs (curr+1) (by omega) (out.push (xs.get curr he))
    · rw [dite_eq_right he,List.drop_eq_nil_of_le (by rw [eraseVec_length];omega)]
      simpa only [eraseVec_push,List.append_assoc,List.singleton_append,AIG.mkConstCached,List.headD_nil] using
        extend_go_rel hr xs (curr+1) (by omega) (out.push (g.mkConstCached false))
  · rw [dite_eq_right hi]
    have he : curr=v:=by omega
    subst curr
    simp only [Nat.sub_self,List.range'_zero,List.map_nil,List.append_nil]
    exact ⟨hr,rfl⟩
termination_by v-curr
lemma extend_rel {n w v : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (r,extend (eraseVec xs) v) (blastZeroExtend (newWidth:=v) g ⟨w,xs⟩) := by
  simpa only [blastZeroExtend,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,List.nil_append,
    extend,Nat.sub_zero,List.range_eq_range'] using
    extend_go_rel (v:=v) hr xs 0 (Nat.zero_le _) (.emptyWithCapacity v)
def shiftConcat (xs : List Ref) (a : Ref) : List Ref:=extend (a::xs) xs.length
lemma shiftConcat_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (a : AIG.Ref g) :
    VecRel (r,shiftConcat (eraseVec xs) (a.gate,a.invert)) (blastUdiv.blastShiftConcat g ⟨xs,a⟩) := by
  have hh:=extend_rel (v:=w) hr ((AIG.RefVec.empty.push a).append xs)
  simpa only [eraseVec_append,eraseVec_push,eraseVec_empty,List.nil_append,List.singleton_append,
    shiftConcat,eraseVec_length,blastUdiv.blastShiftConcat,AIG.RefVec.emptyWithCapacity_eq] using hh
lemma shiftConcat_length (xs : List Ref) (a : Ref) : (shiftConcat xs a).length=xs.length:=extend_length _ _
lemma shiftConcat_refs {B : ℕ} {xs : List Ref} {a : Ref} (hx : RefsBound B xs) (ha : a.1≤B) :
    RefsBound B (shiftConcat xs a) := by
  refine ⟨by simpa only [shiftConcat_length] using hx.1,?_⟩
  intro b hb
  obtain ⟨i,_,rfl⟩:=List.mem_map.mp hb
  cases i with
  | zero=>simpa using ha
  | succ i=>simpa using hx.get i
namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def extendP : Procedure (prodCode unaryCode (listCode refCode)) (listCode refCode)
    (fun x=>extend x.2 x.1):=
  tabulate (f:=fun (xs : List Ref) i=>(xs.drop i).headD (0,false)) (0,false)
    ((listGet refCode (0,false)).comp
      ((unaryToBits.comp (first unaryCode (listCode refCode))).pair (second unaryCode (listCode refCode))))
noncomputable def shiftConcatP : Procedure (prodCode (listCode refCode) refCode) (listCode refCode)
    (fun x=>shiftConcat x.1 x.2) := by
  let xs:=first (listCode refCode) refCode
  let a:=second (listCode refCode) refCode
  exact extendP.comp (((listUnaryLength refCode (0,false)).comp xs).pair
    ((listCons refCode).comp (a.pair xs)))
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

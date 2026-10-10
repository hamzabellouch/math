import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGAddBounded

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def notVec (xs : List Ref) : List Ref:=xs.map notRef
lemma notMap_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) (curr : ℕ) (hc : curr≤w) (out : AIG.RefVec g curr) :
    VecRel (r,eraseVec out++notVec ((eraseVec xs).drop curr))
      (AIG.RefVec.map.go g curr hc out xs AIG.mkNotCached) := by
  rw [AIG.RefVec.map.go]
  by_cases hi : curr<w
  · rw [dite_eq_left hi]
    have hh:=notMap_rel hr xs (curr+1) (by omega) (out.push (xs.get curr hi).not)
    have hl : curr<(eraseVec xs).length:=by simpa only [eraseVec_length] using hi
    rw [List.drop_eq_getElem_cons hl]
    have he : (eraseVec xs)[curr]'hl=((xs.get curr hi).gate,(xs.get curr hi).invert):=by simp [eraseVec]
    rw [he]
    simpa only [notVec,List.map_cons,eraseVec_push,AIG.mkNotCached,AIG.RefVec.cast,AIG.RefVec.cast',AIG.Ref.not,AIG.Ref.flip,
      Bool.true_xor,notRef,List.append_assoc,List.singleton_append] using hh
  · rw [dite_eq_right hi]
    have he : curr=w:=by omega
    subst curr
    rw [List.drop_eq_nil_of_le (by rw [eraseVec_length])]
    simp only [notVec,List.map_nil,List.append_nil]
    exact ⟨hr,rfl⟩
termination_by w-curr
lemma notVec_rel {n w : ℕ} {r : Graph} {g : AIG (Fin n)} (hr : Rel r g)
    (xs : AIG.RefVec g w) : VecRel (r,notVec (eraseVec xs)) (blastNot g xs) := by
  simpa only [blastNot,AIG.RefVec.map,AIG.RefVec.emptyWithCapacity_eq,eraseVec_empty,
    List.nil_append,List.drop_zero] using notMap_rel hr xs 0 (Nat.zero_le _) (.emptyWithCapacity w)
lemma notVec_length (xs : List Ref) : (notVec xs).length=xs.length:=List.length_map _
lemma notVec_refs {B : ℕ} {xs : List Ref} (h : RefsBound B xs) : RefsBound B (notVec xs) := by
  refine ⟨by simpa only [notVec_length] using h.1,?_⟩
  intro a ha
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
  exact h.2 b hb
namespace Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def notVecP : Procedure (listCode refCode) (listCode refCode) notVec:=
  listMap (0,false) (0,false) notRefP
end Emission
end ExactQuantumFactoring.NativeAIG

end


end OAI

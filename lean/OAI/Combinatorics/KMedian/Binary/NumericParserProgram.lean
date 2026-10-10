import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic
import OAI.Combinatorics.KMedian.Binary.BinaryBooleanLists

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem take_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem drop_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩
@[fun_prop] theorem value_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩
@[fun_prop] theorem signed_poly : Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) := ⟨intFromParts⟩
@[fun_prop] theorem mkRat_poly : Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨mkRational⟩
def width (xs : List Bool) : ℕ := xs.findIdx Bool.not
@[fun_prop] theorem width_poly : Poly width := by unfold width; apply list_findIdx <;> fun_prop
def natRead (xs : List Bool) : ℕ × List Bool :=
  (Word.value ((xs.drop (width xs+1)).take (width xs)),xs.drop (width xs+1+width xs))
@[fun_prop] theorem natRead_poly : Poly natRead := by
  have hd : Poly (fun xs : List Bool => xs.drop (width xs+1)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1)) (by fun_prop)
  have ht : Poly (fun xs : List Bool => (xs.drop (width xs+1)).take (width xs)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.take x.2) take_poly (pair hd width_poly)
  exact pair (Poly.comp value_poly ht) (Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1+width xs)) (by fun_prop))
 theorem prefix_width (n : ℕ) (xs : List Bool) : width (List.replicate n true++false::xs)=n := by
  induction n with
  | zero => simp [width,List.findIdx_cons]
  | succ n ih => simp only [List.replicate_succ,List.cons_append,width,List.findIdx_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte]; exact congrArg Nat.succ ih
 theorem natRead_append (n : ℕ) (xs : List Bool) : natRead (encodeNat n++xs)=(n,xs) := by
  unfold natRead
  have hw : width (encodeNat n++xs)=n.bits.length := by
    simpa only [encodeNat,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using prefix_width n.bits.length (n.bits++xs)
  rw [hw]
  have hd : (encodeNat n++xs).drop (n.bits.length+1)=n.bits++xs := by
    simp [encodeNat,List.drop_append,List.append_assoc]
  rw [hd,show (encodeNat n++xs).drop (n.bits.length+1+n.bits.length)=xs from by
    rw [← List.drop_drop,hd,List.drop_left]]
  simp only [List.take_left,Word.value_bits]
 theorem natRead_rest_length (xs : List Bool) : (natRead xs).2.length≤xs.length := by
  simp only [natRead,List.length_drop]; omega
def ratRead (xs : List Bool) : ℚ × List Bool :=
  let a := natRead xs.tail
  let b := natRead a.2
  (mkRat (Signed.value (xs.head?.getD false) a.1) b.1,b.2)
@[fun_prop] theorem ratRead_poly : Poly ratRead := by unfold ratRead; fun_prop
 theorem ratRead_append (q : ℚ) (xs : List Bool) : ratRead (encodeRat q++xs)=(q,xs) := by
  simp only [ratRead,encodeRat,List.append_assoc,List.cons_append,List.tail_cons,List.head?_cons,Option.getD_some,List.nil_append,natRead_append]
  rw [show Signed.value (decide (q.num<0)) q.num.natAbs=q.num from Signed.value_parts q.num]
  rw [Rat.mkRat_eq_div,q.num_div_den]
 theorem ratRead_rest_length (xs : List Bool) : (ratRead xs).2.length≤xs.length :=
  (natRead_rest_length _).trans ((natRead_rest_length _).trans (by simp only [List.length_tail]; omega))
end MetricKMedian.InputParser
end

end OAI

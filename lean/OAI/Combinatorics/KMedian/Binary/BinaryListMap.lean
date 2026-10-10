import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryListFold
import OAI.Combinatorics.KMedian.Binary.BinaryAddition
import OAI.Combinatorics.KMedian.Binary.BinaryNatural

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListAlgorithms
variable {α β : Type}
 theorem pushMap (f : α → β) (as : List α) (bs : List β) :
    as.foldl (fun bs a => f a::bs) bs=(as.map f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons,ih,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem pushFilter (f : α → Bool) (as bs : List α) :
    as.foldl (fun bs a => if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons,List.filter_cons]
      cases f a <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem count (as : List α) (n : ℕ) : as.foldl (fun n _ => n+1) n=n+as.length := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

 theorem all (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b && p a) b=(b && as.all p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.all_cons,Bool.and_assoc]

 theorem any (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b || p a) b=(b || as.any p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.any_cons,Bool.or_assoc]
end ListAlgorithms

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMap (P : PolyProgram ea eb f) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  let step : PolyProgram (encodePair (encodeList eb) ea) (encodeList eb) (fun x => f x.2::x.1) :=
    (((P.second (encodeList eb)).comp (exchange (encodeList eb) eb)).comp (listCons eb)).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (X*(2*P.sizeBound+1)+X) (by
    intro as bs pre suf he
    simp only [ListAlgorithms.pushMap,EncodedList.append,List.length_append,EncodedList.reverse_length]
    let L := (encodePair (encodeList ea) (encodeList eb) (as,bs)).length
    have hpre : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    have hlen : pre.length ≤ L := by
      have hp := EncodedList.length_le ea pre
      simp only [L,encodePair_length]; omega
    have hbs : (encodeList eb bs).length ≤ L := by simp only [L,encodePair_length]; omega
    have hh := EncodedList.length_bound eb (pre.map f) (P.sizeBound.eval L) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound a).trans
      apply polynomial_eval_mono
      have hmem := EncodedList.member_length ea pre a ha
      simp only [L,encodePair_length]; omega)
    simp only [List.length_map] at hh
    simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    change _ ≤ L*(2*P.sizeBound.eval L+1)+L
    nlinarith)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList eb) [])
  exact ((start.comp fold).comp (listReverse eb (f a0))).congr _ (fun as => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushMap,List.append_nil,List.reverse_reverse])

noncomputable def listFilter {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList ea) (List.filter p) := by
  let first := fst (encodeList ea) ea
  let test := (snd (encodeList ea) ea).comp P
  let push := (exchange (encodeList ea) ea).comp (listCons ea)
  let step : PolyProgram (encodePair (encodeList ea) ea) (encodeList ea) (fun x => if p x.2 then x.2::x.1 else x.1) :=
    (ite test first push).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 1 (by
    intro bs a
    simp only [one_mul]
    split_ifs
    · rw [EncodedList.cons_length]; omega
    · omega)
  exact ((((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp fold).comp (listReverse ea a0)).congr _
    (fun as => by simp only [Function.comp_apply,id_eq,ListAlgorithms.pushFilter,List.append_nil,List.reverse_reverse])

noncomputable def listLength (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits List.length := by
  let step : PolyProgram (encodePair Nat.bits ea) Nat.bits (fun x : ℕ × α => x.1+1) :=
    (((fst Nat.bits ea).fanout (constant (encodePair Nat.bits ea) Nat.bits 1)).comp natAdd).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 2 (by
    intro n a
    have h := NatBinary.add_length n 1
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone] at h
    dsimp only
    omega)
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Nat.zero_add] using ListAlgorithms.count as 0)

noncomputable def listAll {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.all p) := by
  let step := (P.second encodeBool).comp boolAnd
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool true)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.true_and] using ListAlgorithms.all p as true)

noncomputable def listAny {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.any p) := by
  let step := (P.second encodeBool).comp boolOr
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool false)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.false_or] using ListAlgorithms.any p as false)
end PolyProgram
end MetricKMedian.Binary
end

end OAI

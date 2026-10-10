import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListContext
import OAI.Combinatorics.KMedian.Binary.BinaryListExtras
import OAI.Combinatorics.KMedian.Binary.BinaryListMap
import OAI.Combinatorics.KMedian.Binary.BinaryListIndices
import OAI.Combinatorics.KMedian.Binary.BinaryListIndex
import OAI.Combinatorics.KMedian.Binary.BinaryListZip
import OAI.Combinatorics.KMedian.Optimization.LPListFacts

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
class Coding (α : Type) where
  encode : α → List Bool
abbrev enc {α : Type} [Coding α] : α → List Bool := Coding.encode
instance : Coding ℕ := ⟨Nat.bits⟩
instance : Coding ℤ := ⟨Signed.encode⟩
instance : Coding ℚ := ⟨Ratio.encode⟩
instance : Coding Bool := ⟨encodeBool⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α × β) := ⟨encodePair enc enc⟩
instance {α : Type} [Coding α] : Coding (List α) := ⟨encodeList enc⟩

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (PolyProgram enc enc f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def program {f : α → β} (h : Poly f) : PolyProgram enc enc f := Classical.choice h

theorem of_program {f : α → β} (p : PolyProgram enc enc f) : Poly f := ⟨p⟩

@[fun_prop] theorem identity : Poly (id : α → α) := ⟨PolyProgram.identity enc⟩
@[fun_prop] theorem const (b : β) : Poly (fun _ : α => b) := ⟨PolyProgram.constant enc enc b⟩
@[fun_prop] theorem comp {f : β → γ} {g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => f (g a)) :=
  ⟨hg.program.comp hf.program⟩
@[fun_prop] theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) : Poly (fun a => (f a,g a)) :=
  ⟨hf.program.fanout hg.program⟩
@[fun_prop] theorem fst : Poly (Prod.fst : α × β → α) := ⟨PolyProgram.fst enc enc⟩
@[fun_prop] theorem snd : Poly (Prod.snd : α × β → β) := ⟨PolyProgram.snd enc enc⟩
@[fun_prop] theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem list_map [Inhabited β] [Inhabited γ] {f : α → β → γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default default)⟩

@[fun_prop] theorem rat_add : Poly (fun x : ℚ × ℚ => x.1+x.2) := ⟨ratAdd⟩
@[fun_prop] theorem rat_sub : Poly (fun x : ℚ × ℚ => x.1-x.2) := ⟨ratSub⟩
@[fun_prop] theorem rat_mul : Poly (fun x : ℚ × ℚ => x.1*x.2) := ⟨ratMul⟩
@[fun_prop] theorem rat_div : Poly (fun x : ℚ × ℚ => x.1/x.2) := ⟨ratDiv⟩
@[fun_prop] theorem rat_lt : Poly (fun x : ℚ × ℚ => decide (x.1<x.2)) := ⟨ratLT⟩
@[fun_prop] theorem rat_le : Poly (fun x : ℚ × ℚ => decide (x.1≤x.2)) := ⟨ratLE⟩
@[fun_prop] theorem rat_eq : Poly (fun x : ℚ × ℚ => decide (x.1=x.2)) := ⟨ratEQ⟩
@[fun_prop] theorem rat_min : Poly (fun x : ℚ × ℚ => min x.1 x.2) := ⟨LPBinary.Program.ratMin⟩
@[fun_prop] theorem rat_max : Poly (fun x : ℚ × ℚ => max x.1 x.2) := ⟨LPBinary.Program.ratMax⟩
@[fun_prop] theorem nat_add : Poly (fun x : ℕ × ℕ => x.1+x.2) := ⟨natAdd⟩
@[fun_prop] theorem nat_sub : Poly (fun x : ℕ × ℕ => x.1-x.2) := ⟨natSub⟩
@[fun_prop] theorem nat_mul : Poly (fun x : ℕ × ℕ => x.1*x.2) := ⟨natMul⟩
@[fun_prop] theorem nat_lt : Poly (fun x : ℕ × ℕ => decide (x.1<x.2)) := ⟨natLT⟩
@[fun_prop] theorem nat_le : Poly (fun x : ℕ × ℕ => decide (x.1≤x.2)) := ⟨natLE⟩
@[fun_prop] theorem nat_eq : Poly (fun x : ℕ × ℕ => decide (x.1=x.2)) := ⟨natEQ⟩
@[fun_prop] theorem bool_and : Poly (fun x : Bool × Bool => x.1 && x.2) := ⟨boolAnd⟩
@[fun_prop] theorem bool_or : Poly (fun x : Bool × Bool => x.1 || x.2) := ⟨boolOr⟩
@[fun_prop] theorem rat_neg : Poly (fun x : ℚ => -x) := ⟨ratNeg⟩
@[fun_prop] theorem bool_not : Poly (fun x : Bool => !x) := ⟨boolNot⟩
@[fun_prop] theorem rat_ofNat : Poly (fun x : ℕ => (x:ℚ)) := ⟨ratOfNat⟩
@[fun_prop] theorem rat_ofInt : Poly (fun x : ℤ => (x:ℚ)) := ⟨ratOfInt⟩

@[fun_prop] theorem list_length [Inhabited α] : Poly (List.length : List α → ℕ) := ⟨listLength enc default⟩
@[fun_prop] theorem list_indices [Inhabited α] : Poly (fun xs : List α => List.range xs.length) := ⟨listIndices enc default⟩
@[fun_prop] theorem list_getD (a0 : α) : Poly (fun x : List α × ℕ => x.1[x.2]?.getD a0) := ⟨listGetD enc a0⟩
@[fun_prop] theorem list_head (a0 : α) : Poly (fun xs : List α => xs.head?.getD a0) := ⟨listHead enc a0⟩
@[fun_prop] theorem list_tail [Inhabited α] : Poly (List.tail : List α → List α) := ⟨listTail enc default⟩
@[fun_prop] theorem list_empty : Poly (List.isEmpty : List α → Bool) := ⟨listIsEmpty enc⟩
@[fun_prop] theorem list_append [Inhabited α] : Poly (fun x : List α × List α => x.1++x.2) := ⟨listAppend enc default⟩
@[fun_prop] theorem list_cons : Poly (fun x : α × List α => x.1::x.2) := ⟨listCons enc⟩
@[fun_prop] theorem list_zip [Inhabited α] [Inhabited β] : Poly (fun x : List α × List β => x.1.zip x.2) := ⟨listZip enc enc default default⟩
@[fun_prop] theorem list_filter [Inhabited α] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).filter (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFilterWith default default)⟩
@[fun_prop] theorem list_findIdx [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).findIdx (f x)) := by
  let tests := ((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default false)
  exact ⟨(tests.comp (listFindIdx (PolyProgram.identity encodeBool) false)).congr _ (fun _ => by
    simp only [Function.comp_def,List.findIdx_map,id_eq])⟩

@[fun_prop] theorem list_getD_comp (a0 : β) {xs : α → List β} {i : α → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun x => (xs x)[i x]?.getD a0) :=
  comp (list_getD a0) (pair hx hi)
@[fun_prop] theorem list_head_comp (a0 : β) {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).head?.getD a0) := comp (list_head a0) hx

@[fun_prop] theorem rat_lt_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp rat_lt (pair hf hg)
@[fun_prop] theorem rat_le_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp rat_le (pair hf hg)
@[fun_prop] theorem rat_eq_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp rat_eq (pair hf hg)
@[fun_prop] theorem nat_lt_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp nat_lt (pair hf hg)
@[fun_prop] theorem nat_le_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp nat_le (pair hf hg)
@[fun_prop] theorem nat_eq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp nat_eq (pair hf hg)
@[fun_prop] theorem ite_prop {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  exact ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => by simp only [decide_eq_true_eq])⟩

@[fun_prop] theorem list_flatMap [Inhabited β] [Inhabited γ] {f : α → β → List γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFlatMapWith default default)⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI

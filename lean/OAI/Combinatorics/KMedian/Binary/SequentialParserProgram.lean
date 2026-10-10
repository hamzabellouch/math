import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic
import OAI.Combinatorics.KMedian.Binary.BinaryBooleanLists

namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
section Generic
variable {α : Type} [Coding α] [Inhabited α] (read : List Bool → α × List Bool)
abbrev State := List Bool × List α
def parseStep (x : State (α:=α) × Unit) : State (α:=α) :=
  let s := read x.1.1
  (s.2,s.1::x.1.2)
 omit [Inhabited α] in
 theorem parseStep_poly (h : Poly read) : Poly (parseStep read) := by
  unfold parseStep
  have hh : Poly (fun x : State (α:=α) × Unit => read x.1.1) := Poly.comp h (by fun_prop)
  have ha : Poly (fun x : State (α:=α) × Unit => (read x.1.1).1 :: x.1.2) :=
    Poly.comp (f:=fun y : α × List α => y.1::y.2) list_cons (g:=fun x : State (α:=α) × Unit => ((read x.1.1).1,x.1.2)) (by fun_prop)
  exact pair (by fun_prop) ha
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseBound : Polynomial ℕ := X+X*(2*P.sizeBound+1)
 omit [Inhabited α] in
 include hrest in
 theorem parseFold_size (as : List Unit) (b : State (α:=α)) :
    let out := as.foldl (fun b a => parseStep read (b,a)) b
    out.1.length≤b.1.length ∧
    (enc out.2).length≤(enc b.2).length+as.length*(2*P.sizeBound.eval (enc b.1).length+1) := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,List.length_nil,zero_mul,add_zero]; exact ⟨le_rfl,le_rfl⟩
  | cons a as ih =>
    have hh := ih (parseStep read (b,a))
    have hr := hrest b.1
    have hs := P.length_bound b.1
    have he : (enc ((read b.1).1)).length ≤ P.sizeBound.eval (enc b.1).length := by
      change (encodePair enc enc (read b.1)).length≤_ at hs
      rw [encodePair_length] at hs
      omega
    have hp : P.sizeBound.eval (enc (read b.1).2).length≤P.sizeBound.eval (enc b.1).length := by
      apply polynomial_eval_mono
      change (encodeList encodeBool (read b.1).2).length≤(encodeList encodeBool b.1).length
      rw [BooleanLists.length,BooleanLists.length]
      omega
    dsimp only [parseStep] at hh
    simp only [List.foldl_cons,List.length_cons]
    refine ⟨hh.1.trans hr,?_⟩
    have hc : (enc ((read b.1).1::b.2)).length=2*(enc (read b.1).1).length+1+(enc b.2).length := EncodedList.cons_length _ _ _
    rw [hc] at hh
    exact hh.2.trans (by nlinarith)
noncomputable def foldProgram : PolyProgram enc enc
    (fun x : List Unit × State (α:=α) => x.1.foldl (fun b a => parseStep read (b,a)) x.2) :=
  (parseStep_poly read ⟨P⟩).program.listFold () (parseBound read P) (by
    intro as b pre suf he
    have hh := parseFold_size read P hrest pre b
    let L := (enc (as,b)).length
    have hb : (enc b).length≤L := by
      dsimp only [L]
      change (enc b).length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hp : pre.length≤L := by
      have ha := EncodedList.length_le (enc : Unit → List Bool) as
      have hl : pre.length≤as.length := by rw [he,List.length_append]; omega
      change as.length≤(enc as).length at ha
      dsimp only [L]
      change pre.length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hx : (enc b.1).length≤L := by
      change (encodePair enc enc b).length≤L at hb
      rw [encodePair_length] at hb; omega
    have hq := polynomial_eval_mono P.sizeBound hx
    have hr : (enc (pre.foldl (fun b a => parseStep read (b,a)) b).1).length≤(enc b.1).length := by
      change (encodeList encodeBool _).length≤(encodeList encodeBool _).length
      rw [BooleanLists.length,BooleanLists.length]; omega
    change (encodePair enc enc _).length≤_
    rw [encodePair_length]
    change (encodePair enc enc b).length≤L at hb
    rw [encodePair_length] at hb
    simp only [parseBound,eval_add,eval_X,eval_mul,eval_ofNat,eval_one]
    change _≤L+L*(2*P.sizeBound.eval L+1)
    have hm := Nat.mul_le_mul hp (show 2*P.sizeBound.eval (enc b.1).length+1≤2*P.sizeBound.eval L+1 by omega)
    have hh2 := hh.2
    omega)
def parse (x : List Unit × List Bool) : List α × List Bool :=
  let s := x.1.foldl (fun b a => parseStep read (b,a)) (x.2,[])
  (s.2.reverse,s.1)
noncomputable def parseProgram : PolyProgram enc enc (parse read) := by
  have h : Poly (fun x : List Unit × List Bool => (x.1,(x.2,([] : List α)))) := by fun_prop
  have hv : Poly (List.reverse : List α → List α) := ⟨listReverse enc default⟩
  have g : Poly (fun x : State (α:=α) => (x.2.reverse,x.1)) := pair (Poly.comp hv snd) fst
  exact h.program.comp (foldProgram read P hrest) |>.comp g.program
 omit [Coding α] [Inhabited α] in
 theorem parse_fold_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) (acc : List α) :
    (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,acc)=
      (xs,as.reverse++acc) := by
  induction as generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons,List.replicate_succ,List.map_cons,List.flatten_cons,List.append_assoc,
      List.foldl_cons,parseStep,hr]
    change (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,a::acc)=_
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
 omit [Coding α] [Inhabited α] in
 theorem parse_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) :
    parse read (List.replicate as.length (),(as.map put).flatten++xs)=(as,xs) := by
  unfold parse
  rw [parse_fold_encoded read put hr]
  simp
end Generic
end MetricKMedian.InputParser
end

end OAI

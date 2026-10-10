import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram
import Mathlib.Data.List.MinMax

namespace OAI

/-! # Binary scan selecting a greatest weighted edge

The accumulator is either empty or one stored edge. Its binary size is
bounded by the input list size even when capacities are numerically large.
-/

namespace ContingencyTables.WeightedArgmaxProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev Edge := (ℕ×ℕ)×ℕ
abbrev Input := Edge×Option Edge

def advance (z : Input) : Option Edge :=
  match z.2 with
  | none => Option.some z.1
  | Option.some old => if old.2<z.1.2 then Option.some z.1 else Option.some old

private def compareInput (z : Edge×Edge) : ℕ×ℕ := (z.2.2,z.1.2)
private def compareRealizer : Realizer compareInput :=
  pair (composition second second) (composition first second)
private lemma polynomial_compare : PolynomialTime compareRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)

private def chooseRealizer : Realizer (fun z : Edge×Edge=>
    if z.2.2<z.1.2 then Option.some z.1 else Option.some z.2) :=
  (choose (composition compareRealizer less) (composition first some)
    (composition second some)).congr (by
      intro z
      by_cases h : z.2.2<z.1.2 <;> simp [Function.comp_apply,compareInput,h])
private lemma polynomial_choose : PolynomialTime chooseRealizer :=
  polynomial_congr _ (MatchingFPRAS.TreeTyped.polynomial_choose
    (polynomial_composition polynomial_compare polynomial_less)
    (polynomial_composition polynomial_first polynomial_some)
    (polynomial_composition polynomial_second polynomial_some))

def advanceRealizer : Realizer advance :=
  (optionCases some chooseRealizer).congr (by
    rintro ⟨e,o⟩
    cases o <;> rfl)
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_congr _ (polynomial_optionCases polynomial_some polynomial_choose)

private lemma some_weight (e : Edge) :
    weight (Option.some e)=1+weight true+weight e := by
  change weight (true,e)=_
  exact weight_prod _ _

private lemma none_large : 1+weight true≤weight (none : Option Edge) := by decide

lemma advance_weight (e : Edge) (o : Option Edge) :
    weight (advance (e,o))≤weight o+weight e+1 := by
  cases o with
  | none=>
    simp only [advance,some_weight]
    have h := none_large
    omega
  | some a=>
    simp only [advance]
    split <;> simp only [some_weight] <;> omega

lemma fold_weight (xs : List Edge) (o : Option Edge) :
    weight (xs.foldl (fun o e=>advance (e,o)) o)≤weight o+weight xs := by
  induction xs generalizing o with
  | nil=>simp only [List.foldl_nil,weight_nil]; omega
  | cons e xs ih=>
    have h := ih (advance (e,o))
    have hs := advance_weight e o
    simp only [List.foldl_cons,weight_cons]
    omega

lemma polynomial_scan : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance X
  intro xs o pre post he
  have hp := weight_prefix he
  have hf := fold_weight pre o
  simp only [eval_X,weight_prod]
  omega

def best (xs : List Edge) : Option Edge := xs.foldl (fun o e=>advance (e,o)) none
def bestRealizer : Realizer best :=
  composition (f := fun xs : List Edge=>(xs,(none : Option Edge)))
    (g := fun z : List Edge×Option Edge=>z.1.foldl (fun o e=>advance (e,o)) z.2)
    (pair identity (constant none)) (fold advanceRealizer)
lemma polynomial_best : PolynomialTime bestRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant none))
    polynomial_scan

lemma best_argmax (xs : List Edge) : best xs=xs.argmax Prod.snd := by
  have hf : (fun o e=>advance (e,o))=
      List.argAux (fun a b : Edge=>b.2<a.2) := by
    funext o e
    cases o <;> rfl
  unfold best List.argmax
  rw [hf]

lemma best_mem {xs : List Edge} {e : Edge} (he : best xs=some e) : e∈xs := by
  rw [best_argmax] at he
  exact List.argmax_mem he

lemma best_max {xs : List Edge} {e : Edge} (he : best xs=some e)
    {a : Edge} (ha : a∈xs) : a.2≤e.2 := by
  rw [best_argmax] at he
  exact List.le_of_mem_argmax (f := Prod.snd) ha he

lemma best_none (xs : List Edge) : best xs=none ↔ xs=[] := by
  rw [best_argmax,List.argmax_eq_none]

end ContingencyTables.WeightedArgmaxProgram

end OAI

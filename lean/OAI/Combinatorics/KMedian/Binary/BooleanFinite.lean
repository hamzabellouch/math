import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace FiniteTransducer
variable {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool) (f : α → β)

noncomputable def prefixes : Finset (List Bool) :=
  univ.biUnion (fun a => (ea a).inits.toFinset)

 theorem mem_prefixes (a : α) (xs ys : List Bool) (h : xs++ys=ea a) : xs∈prefixes ea := by
  classical
  apply mem_biUnion.mpr
  refine ⟨a,mem_univ _,List.mem_toFinset.mpr ?_⟩
  exact (List.mem_inits _ _).mpr ⟨ys,h⟩

abbrev Q := Option {xs : List Bool // xs∈prefixes ea}

noncomputable def state (xs : List Bool) : Q ea :=
  if h : xs∈prefixes ea then some ⟨xs,h⟩ else none

noncomputable abbrev table : Transducer where
  Q := Q ea
  initial := state ea []
  next q b := (match q with | none => none | some xs => state ea (xs.val++[b]),[])
  finish q := match q with
    | none => []
    | some xs => if h : ∃ a, ea a=xs.val then eb (f (Classical.choose h)) else []

 theorem next_state (xs : List Bool) (b : Bool) (h : xs∈prefixes ea) :
    (table ea eb f).next (state ea xs) b=(state ea (xs++[b]),[]) := by
  simp only [table,state,dite_eq_left h]

 theorem finish_state (a : α) (hinj : Injective ea) :
    (table ea eb f).finish (state ea (ea a))=eb (f a) := by
  have hm := mem_prefixes ea a (ea a) [] (List.append_nil _)
  have hex : ∃ a', ea a'=ea a := ⟨a,rfl⟩
  simp only [state,dite_eq_left hm,dite_eq_left hex]
  have he := Classical.choose_spec hex
  rw [hinj he]

 theorem run_state (a : α) (hinj : Injective ea) (xs ys : List Bool) (h : xs++ys=ea a) :
    (table ea eb f).run (state ea xs) ys=eb (f a) := by
  induction ys generalizing xs with
  | nil =>
      have he : xs=ea a := by simpa only [List.append_nil] using h
      rw [he]
      exact finish_state ea eb f a hinj
  | cons b ys ih =>
      change ((table ea eb f).next (state ea xs) b).2 ++
        (table ea eb f).run ((table ea eb f).next (state ea xs) b).1 ys = _
      rw [next_state ea eb f xs b (mem_prefixes ea a xs (b::ys) h),List.nil_append]
      apply ih
      simpa only [List.append_assoc,List.singleton_append] using h

noncomputable def program (hinj : Injective ea) : PolyProgram ea eb f :=
  (table ea eb f).program.of_word (fun a =>
    run_state ea eb f a hinj [] (ea a) rfl)

end FiniteTransducer

 theorem encodeBool_injective : Injective encodeBool := by
  intro a b h
  simpa only [encodeBool,List.cons.injEq,true_and,and_true] using h

 theorem quote_injective : Injective quote := by
  intro xs ys h
  have hh := congrArg ((WordTransducer.projecting false).run none) h
  have hx := WordTransducer.projecting_pair false xs []
  have hy := WordTransducer.projecting_pair false ys []
  simp only [List.append_nil,Bool.false_eq_true,ite_false] at hx hy
  rwa [hx,hy] at hh

 theorem encodePair_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Injective ea) (hb : Injective eb) : Injective (encodePair ea eb) := by
  intro a b h
  have hx := congrArg ((WordTransducer.projecting false).run none) h
  have hy := congrArg ((WordTransducer.projecting true).run none) h
  simp only [encodePair,WordTransducer.projecting_pair,Bool.false_eq_true,ite_false,ite_true] at hx hy
  exact Prod.ext (ha hx) (hb hy)

namespace PolyProgram

noncomputable def boolFunction {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (hinj : Injective ea) : PolyProgram ea eb f :=
  FiniteTransducer.program ea eb f hinj

noncomputable def boolNot : PolyProgram encodeBool encodeBool Bool.not :=
  boolFunction _ _ _ encodeBool_injective
noncomputable def boolAnd : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 && x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolOr : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 || x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI

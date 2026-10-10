import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauDirectories

namespace OAI

section Inline_PCPTableauDirectoryProgram
namespace MetricKMedian.PCP.Compiler.TableauDirectory
open Binary Binary.Automatic
open scoped Classical

@[fun_prop] lemma poly_append_comp {X A : Type} [Coding X] [Coding A] [Inhabited A]
    {f g : X→List A} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x++g x) :=
  Poly.list_append.comp (Poly.pair hf hg)
@[fun_prop] lemma poly_and_comp {X : Type} [Coding X] {f g : X→Bool}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => f x && g x) :=
  Poly.bool_and.comp (Poly.pair hf hg)
variable {K : Type} [Fintype K] [DecidableEq K] [Coding K] [Hardcoded K] [Inhabited K] (k0 : K)
@[fun_prop] lemma poly_range_succ : Poly (fun xs : List Unit => List.range (xs.length+1)) := by
  have h : Poly (fun xs : List Unit => List.range (xs++[()]).length) := Poly.list_indices.comp (Poly.list_append.comp (Poly.pair Poly.identity (Automatic.Poly.const [()])))
  simpa only [List.length_append,List.length_singleton] using h
@[fun_prop] lemma poly_range_comp {X A : Type} [Coding X] [Coding A] [Inhabited A]
    {f : X→List A} (hf : Poly f) : Poly (fun x => List.range (f x).length) := Poly.list_indices.comp hf
@[fun_prop] lemma poly_range_succ_comp {X : Type} [Coding X] {f : X→List Unit}
    (hf : Poly f) : Poly (fun x => List.range ((f x).length+1)) := poly_range_succ.comp hf
omit [DecidableEq K] [Hardcoded K] in
lemma poly_vars : Poly (fun p : List Unit×List Unit => vars k0 p.1.length p.2.length) := by
  have ht : Poly (fun p : List Unit×List Unit => List.range (p.1.length+1)) := poly_range_succ.comp Poly.fst
  have hl : Poly (fun p : List Unit×List Unit => List.range (p.2.length+1)) := poly_range_succ.comp Poly.snd
  have ht0 : Poly (fun p : List Unit×List Unit => List.range p.1.length) := Poly.list_indices.comp Poly.fst
  unfold vars
  repeat' first | assumption | exact Automatic.Poly.const _ | apply poly_append_comp | apply Poly.list_map | apply Poly.list_flatMap | assumption
  all_goals fun_prop
omit [DecidableEq K] [Hardcoded K] in
lemma poly_clauses : Poly (fun p : List Unit×List Unit => clauses k0 p.1.length p.2.length) := by
  have ht : Poly (fun p : List Unit×List Unit => List.range (p.1.length+1)) := poly_range_succ.comp Poly.fst
  have hl : Poly (fun p : List Unit×List Unit => List.range (p.2.length+1)) := poly_range_succ.comp Poly.snd
  have ht0 : Poly (fun p : List Unit×List Unit => List.range p.1.length) := Poly.list_indices.comp Poly.fst
  have hl0 : Poly (fun p : List Unit×List Unit => List.range p.2.length) := Poly.list_indices.comp Poly.snd
  unfold clauses
  repeat' first | assumption | exact Automatic.Poly.const _ | apply poly_append_comp | apply Poly.list_map | apply Poly.list_flatMap | assumption
  all_goals fun_prop
omit [DecidableEq K] [Hardcoded K] in
lemma poly_boundaries : Poly (fun xs : List Unit => boundaries k0 xs.length) := by
  have hl : Poly (fun xs : List Unit => List.range (xs.length+1)) := poly_range_succ
  unfold boundaries
  repeat' first | assumption | exact Automatic.Poly.const _ | apply poly_append_comp | apply Poly.list_map | apply Poly.list_flatMap | assumption
  all_goals fun_prop
omit [DecidableEq K] [Hardcoded K] in
lemma poly_tests : Poly (fun p : List Unit×List Unit => tests k0 p.1.length p.2.length) :=
  Poly.list_append.comp (Poly.pair (poly_clauses k0) ((poly_boundaries k0).comp Poly.snd))
omit [Inhabited K] in
lemma poly_code_eq (n : ℕ) : Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) => decide (p.1=p.2)) := by
  have hf : Poly (fun p : Fin n×Fin n => decide (p.1=p.2)) := hardcoded _
  have hk : Poly (fun p : K×K => decide (p.1=p.2)) := hardcoded _
  simpa only [Prod.ext_iff,Bool.decide_and] using
    (show Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) =>
      decide (p.1.1=p.2.1) && (decide (p.1.2.1=p.2.2.1) &&
        (decide (p.1.2.2.1=p.2.2.2.1) && decide (p.1.2.2.2=p.2.2.2.2)))) from by
      apply poly_and_comp
      · exact hf.comp (show Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) => (p.1.1,p.2.1)) by fun_prop)
      · apply poly_and_comp
        · fun_prop
        · apply poly_and_comp
          · exact hk.comp (show Poly (fun p : (Fin n×(ℕ×(K×ℕ)))×(Fin n×(ℕ×(K×ℕ))) => (p.1.2.2.1,p.2.2.2.1)) by fun_prop)
          · fun_prop)
end MetricKMedian.PCP.Compiler.TableauDirectory

end Inline_PCPTableauDirectoryProgram

end OAI

import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauBoundary
import OAI.Combinatorics.KMedian.Expanders.CloudPrograms
import OAI.Combinatorics.KMedian.Machines.FiniteCoordinates

namespace OAI

section Inline_PCPFiniteFilterProgram
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

lemma poly_finite_filter {X I : Type} [Coding X] [Fintype I] [Coding (Finset I)]
    (f : X→I→Prop) (h : ∀ i, Poly (fun x=>decide (f x i))) :
    Poly (fun x=>Finset.univ.filter (f x)) := by
  have hh := poly_coordinates (fun x i=>decide (f x i)) h
  have hc : Poly (fun g : I→Bool => Finset.univ.filter (fun i=>g i)) := hardcoded _
  apply poly_congr (hc.comp hh)
  intro x
  simp only [decide_eq_true_eq]
namespace FiniteList
variable {A X : Type} [Fintype A] [Coding A] [Hardcoded A] [Coding X] [Inhabited A]
noncomputable instance optionCoding : Coding (Option A) := finiteCoding _
noncomputable instance optionHardcoded : Hardcoded (Option A) := ⟨fun _ _ _ f=>finite_function f⟩
lemma poly_getElem? : Poly (fun p : List A×ℕ => p.1[p.2]?) := by
  have hs : Poly (some : A→Option A) := hardcoded _
  have hm : Poly (fun p : List A×ℕ => p.1.map some) := Poly.list_map (hs.comp Poly.snd) Poly.fst
  apply poly_congr (Poly.list_getD_comp none hm Poly.snd)
  intro p
  simp only [List.getElem?_map]
  cases p.1[p.2]? <;> rfl
lemma poly_prefixCell (pref : X→List A) (bound : X→ℕ) (v : Option A)
    (hp : Poly pref) (hb : Poly bound) :
    Poly (fun p : X×ℕ=>decide (Tableau.prefixCell (pref p.1) (bound p.1) p.2 v)) := by
  have hg := poly_getElem?.comp (Poly.pair (hp.comp Poly.fst) Poly.snd)
  have he : Poly (fun a : Option A=>decide (v=a)) := hardcoded _
  have hv := he.comp hg
  have h1 : Poly (fun p : X×ℕ=>decide (p.2<(pref p.1).length)) := by fun_prop
  have h2 : Poly (fun p : X×ℕ=>decide ((pref p.1).length+bound p.1≤p.2)) := by fun_prop
  have h : Poly (fun p : X×ℕ=>(!decide (p.2<(pref p.1).length) || decide (v=(pref p.1)[p.2]?)) &&
      (!decide ((pref p.1).length+bound p.1≤p.2) || decide (v=none))) := by fun_prop
  apply poly_congr h
  intro p
  rw [Bool.eq_iff_iff]
  simp [Tableau.prefixCell,Bool.or_eq_true,Bool.and_eq_true,imp_iff_not_or]

end FiniteList
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteFilterProgram

end OAI

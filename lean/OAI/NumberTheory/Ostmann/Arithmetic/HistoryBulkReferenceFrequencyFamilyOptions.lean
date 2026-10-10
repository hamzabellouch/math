import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageRingUnitActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily
open Construction HistoryPairedFrequencyAverage
open scoped BigOperators

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l} {s t : ℤ}

def optionValue (refs : ReferenceFamily sources seed V outside l x y s t)
    (F : ∀fg, SupportedReference sources seed V outside l x y s t fg → ℝ)
    (fg : FrequencyChoices V l × FrequencyChoices V l) : ℝ :=
  (refs fg).elim 0 (F fg)

theorem optionValue_present (refs : ReferenceFamily sources seed V outside l x y s t)
    (F : ∀fg, SupportedReference sources seed V outside l x y s t fg → ℝ)
    (i : Present refs) : optionValue refs F i.val = F i.val (selected refs i) := by
  rcases i with ⟨fg,hfg⟩
  cases he : refs fg with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hfg
  | some r => simp only [optionValue,selected,he,Option.elim_some,Option.get_some]

theorem sum_optionValue_eq_present (refs : ReferenceFamily sources seed V outside l x y s t)
    (F : ∀fg, SupportedReference sources seed V outside l x y s t fg → ℝ) :
    (∑fg, optionValue refs F fg) = ∑i : Present refs, F i.val (selected refs i) := by
  classical
  have he : (∑fg ∈ Finset.univ.filter (fun fg => (refs fg).isSome), optionValue refs F fg) =
      ∑i : Present refs, optionValue refs F i.val :=
    Finset.sum_subtype _ (by simp) _
  rw [←Finset.sum_congr rfl (fun i _ => optionValue_present refs F i), ←he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro fg _ hn
  have hfalse : ¬(refs fg).isSome := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hn
  cases heq : refs fg with
  | none => simp only [optionValue,heq,Option.elim_none]
  | some r => simp only [heq,Option.isSome_some,not_true_eq_false] at hfalse

def referenceUnitAverage (K m : ℕ)
    {fg : FrequencyChoices V l × FrequencyChoices V l}
    (r : SupportedReference sources seed V outside l x y s t fg) : ℝ :=
  canonicalUnitBulkAverage K
    (decodeHistory sources seed V l r.left (assembleHistoryChoices sources seed V l fg.1 x))
    (decodeHistory sources seed V l r.right (assembleHistoryChoices sources seed V l fg.2 y))
    r.left_supported r.right_supported m

def referenceRingUnitAverage (K m : ℕ)
    {fg : FrequencyChoices V l × FrequencyChoices V l}
    (r : SupportedReference sources seed V outside l x y s t fg) : ℝ :=
  canonicalRingUnitBulkAverage K
    (decodeHistory sources seed V l r.left (assembleHistoryChoices sources seed V l fg.1 x))
    (decodeHistory sources seed V l r.right (assembleHistoryChoices sources seed V l fg.2 y))
    r.left_supported r.right_supported m

end Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily

end

end OAI

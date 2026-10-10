import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily
open Construction Conclusion HistoryPairedFrequencyAverage Characters FrequencyTreeSum Filter
open scoped BigOperators

abbrev RootFrequencyIndex (V : ℕ → ℕ) (l : ℕ) :=
  AllowedFrequency V l × (FrequencyChoices V l × FrequencyChoices V l)

abbrev RootReferenceFamily (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) (x y : InternalSourceDraws sources seed l) :=
  (i : RootFrequencyIndex V l) →
    Option (SupportedReference sources seed V outside l x y i.1.val i.1.val i.2)

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l}

def RootPresent (refs : RootReferenceFamily sources seed V outside l x y) :=
  {i : RootFrequencyIndex V l // (refs i).isSome}

instance rootPresentFintype (refs : RootReferenceFamily sources seed V outside l x y) :
    Fintype (RootPresent refs) := by
  classical
  unfold RootPresent
  infer_instance

def rootSelected (refs : RootReferenceFamily sources seed V outside l x y) (i : RootPresent refs) :
    SupportedReference sources seed V outside l x y i.val.1.val i.val.1.val i.val.2 :=
  (refs i.val).get i.property

def rootLeftHistory (refs : RootReferenceFamily sources seed V outside l x y) (i : RootPresent refs) : History l :=
  decodeHistory sources seed V l (rootSelected refs i).left
    (assembleHistoryChoices sources seed V l i.val.2.1 x)

def rootRightHistory (refs : RootReferenceFamily sources seed V outside l x y) (i : RootPresent refs) : History l :=
  decodeHistory sources seed V l (rootSelected refs i).right
    (assembleHistoryChoices sources seed V l i.val.2.2 y)

theorem rootLeftHistory_supported (refs : RootReferenceFamily sources seed V outside l x y) (i : RootPresent refs) :
    (rootLeftHistory refs i).Supported V outside := (rootSelected refs i).left_supported

theorem rootRightHistory_supported (refs : RootReferenceFamily sources seed V outside l x y) (i : RootPresent refs) :
    (rootRightHistory refs i).Supported V outside := (rootSelected refs i).right_supported

theorem root_supported_assignment_injective (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (sources : SourceFamily) (seed : List SourceSlot) (outside : List ℕ) (l : ℕ)
    (x y : InternalSourceDraws sources seed l)
    (refs : RootReferenceFamily sources seed (frequencyBound Bs BD Bz k L) outside l x y) :
    Function.Injective (fun i : RootPresent refs => supportedHistoryAssignment Bs BD Bz k L
      (rootLeftHistory refs i) (rootRightHistory refs i)
      (rootLeftHistory_supported refs i) (rootRightHistory_supported refs i)) := by
  intro i j he
  have hroot := congrArg (FrequencyTreeSum.root (PairedFrequencyActualBudget.pairedRanges Bs BD Bz k L l)) he
  simp only [supportedHistoryAssignment,historyAssignment_root,rootLeftHistory,rootRightHistory,
    decodeHistory_root] at hroot
  have hv := congrArg Prod.fst hroot
  rw [(rootSelected refs i).left_frequency,(rootSelected refs j).left_frequency] at hv
  have hf := supported_assignment_decode_injective Bs BD Bz k L sources seed l outside
    (rootSelected refs i).left (rootSelected refs i).right (rootSelected refs j).left (rootSelected refs j).right
    i.val.2.1 i.val.2.2 j.val.2.1 j.val.2.2 x y x y
    (rootSelected refs i).left_supported (rootSelected refs i).right_supported
    (rootSelected refs j).left_supported (rootSelected refs j).right_supported he
  exact Subtype.ext (Prod.ext (Subtype.ext hv) (Prod.ext hf.1 hf.2))

def rootOptionValue (refs : RootReferenceFamily sources seed V outside l x y)
    (F : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℝ)
    (i : RootFrequencyIndex V l) : ℝ := (refs i).elim 0 (F i)

theorem rootOptionValue_present (refs : RootReferenceFamily sources seed V outside l x y)
    (F : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℝ)
    (i : RootPresent refs) : rootOptionValue refs F i.val = F i.val (rootSelected refs i) := by
  rcases i with ⟨fg,hfg⟩
  cases he : refs fg with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at hfg
  | some r => simp only [rootOptionValue,rootSelected,he,Option.elim_some,Option.get_some]

theorem sum_rootOptionValue_eq_present (refs : RootReferenceFamily sources seed V outside l x y)
    (F : ∀i : RootFrequencyIndex V l, SupportedReference sources seed V outside l x y i.1.val i.1.val i.2 → ℝ) :
    (∑i, rootOptionValue refs F i) = ∑i : RootPresent refs, F i.val (rootSelected refs i) := by
  classical
  have he : (∑i ∈ Finset.univ.filter (fun i => (refs i).isSome), rootOptionValue refs F i) =
      ∑i : RootPresent refs, rootOptionValue refs F i.val :=
    Finset.sum_subtype _ (by simp) _
  rw [←Finset.sum_congr rfl (fun i _ => rootOptionValue_present refs F i), ←he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hn
  have hfalse : ¬(refs i).isSome := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hn
  cases heq : refs i with
  | none => simp only [rootOptionValue,heq,Option.elim_none]
  | some r => simp only [heq,Option.isSome_some,not_true_eq_false] at hfalse

theorem root_reference_frequency_average_eventually {Bs BD Bz : ℝ}
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ K m : ℕ, 0 < m →
      ∀ (sources : SourceFamily) (seed : List SourceSlot) (outside : List ℕ),
      ∀ (x y : InternalSourceDraws sources seed l),
      ∀ refs : RootReferenceFamily sources seed (frequencyBound Bs BD Bz k L) outside l x y,
      (∑i, rootOptionValue refs (fun _ r => referenceUnitAverage K m r) i) ≤
          Real.exp (2 * (2 : ℝ)^l * initialGap Bs k L + ρ * (bulkSize k L : ℝ)) ∧
      (∑i, rootOptionValue refs (fun _ r => referenceRingUnitAverage K m r) i) ≤
          Real.exp (2 * (2 : ℝ)^l * initialGap Bs k L + ρ * (bulkSize k L : ℝ)) := by
  filter_upwards [supported_bulk_frequency_average_eventually hBs hBD hBz hk hρ,
    supported_ringUnit_frequency_average_eventually hBs hBD hBz hk hρ] with L hunit hring
  intro l hl K m hm sources seed outside x y refs
  have hi := root_supported_assignment_injective Bs BD Bz k L sources seed outside l x y refs
  have hu := hunit l hl K m hm (RootPresent refs) (rootLeftHistory refs) (rootRightHistory refs) outside
    (rootLeftHistory_supported refs) (rootRightHistory_supported refs) hi
  have hr := hring l hl K m hm (RootPresent refs) (rootLeftHistory refs) (rootRightHistory refs) outside
    (rootLeftHistory_supported refs) (rootRightHistory_supported refs) hi
  constructor
  · rw [sum_rootOptionValue_eq_present]
    exact hu.1
  · rw [sum_rootOptionValue_eq_present]
    exact hr

end Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily

end

end OAI

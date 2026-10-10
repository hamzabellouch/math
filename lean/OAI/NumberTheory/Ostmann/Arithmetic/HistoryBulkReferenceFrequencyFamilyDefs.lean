import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily
open Construction HistoryPairedFrequencyAverage

structure SupportedReference (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (x y : InternalSourceDraws sources seed l) (s t : ℤ)
    (fg : FrequencyChoices V l × FrequencyChoices V l) where
  left : State
  right : State
  left_frequency : left.frequency = s
  right_frequency : right.frequency = t
  left_matches : Template.Matches (Template.current seed l) left.small
  right_matches : Template.Matches (Template.current seed l) right.small
  left_supported : (decodeHistory sources seed V l left
    (assembleHistoryChoices sources seed V l fg.1 x)).Supported V outside
  right_supported : (decodeHistory sources seed V l right
    (assembleHistoryChoices sources seed V l fg.2 y)).Supported V outside

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {x y : InternalSourceDraws sources seed l} {s t : ℤ}

abbrev ReferenceFamily (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) (x y : InternalSourceDraws sources seed l) (s t : ℤ) :=
  (fg : FrequencyChoices V l × FrequencyChoices V l) →
    Option (SupportedReference sources seed V outside l x y s t fg)

def Present (refs : ReferenceFamily sources seed V outside l x y s t) :=
  {fg : FrequencyChoices V l × FrequencyChoices V l // (refs fg).isSome}

instance presentFintype (refs : ReferenceFamily sources seed V outside l x y s t) :
    Fintype (Present refs) := by
  classical
  unfold Present
  infer_instance

def selected (refs : ReferenceFamily sources seed V outside l x y s t) (i : Present refs) :
    SupportedReference sources seed V outside l x y s t i.val := (refs i.val).get i.property

def leftHistory (refs : ReferenceFamily sources seed V outside l x y s t) (i : Present refs) : History l :=
  decodeHistory sources seed V l (selected refs i).left (assembleHistoryChoices sources seed V l i.val.1 x)

def rightHistory (refs : ReferenceFamily sources seed V outside l x y s t) (i : Present refs) : History l :=
  decodeHistory sources seed V l (selected refs i).right (assembleHistoryChoices sources seed V l i.val.2 y)

theorem leftHistory_supported (refs : ReferenceFamily sources seed V outside l x y s t) (i : Present refs) :
    (leftHistory refs i).Supported V outside := (selected refs i).left_supported

theorem rightHistory_supported (refs : ReferenceFamily sources seed V outside l x y s t) (i : Present refs) :
    (rightHistory refs i).Supported V outside := (selected refs i).right_supported

theorem supported_assignment_injective (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ)
    (sources : SourceFamily) (seed : List SourceSlot) (outside : List ℕ) (l : ℕ)
    (x y : InternalSourceDraws sources seed l) (s t : ℤ)
    (refs : ReferenceFamily sources seed (Conclusion.frequencyBound Bs BD Bz k L) outside l x y s t) :
    Function.Injective (fun i : Present refs => supportedHistoryAssignment Bs BD Bz k L
      (leftHistory refs i) (rightHistory refs i) (leftHistory_supported refs i) (rightHistory_supported refs i)) := by
  intro i j he
  have hf := supported_assignment_decode_injective Bs BD Bz k L sources seed l outside
    (selected refs i).left (selected refs i).right (selected refs j).left (selected refs j).right
    i.val.1 i.val.2 j.val.1 j.val.2 x y x y
    (selected refs i).left_supported (selected refs i).right_supported
    (selected refs j).left_supported (selected refs j).right_supported he
  exact Subtype.ext (Prod.ext hf.1 hf.2)

end Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamily

end

end OAI

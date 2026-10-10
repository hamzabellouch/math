import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceAmplitudeData
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudePriorDefs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators

def sourceWidth {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) : Template.Role → ℕ
  | .word => m+1
  | .pivot j => if hj : j < k then (cfg.2 ⟨j,by omega⟩).length else 0
  | .anchor _ _ => 1
  | .filler => (cfg.2 (Fin.last k)).length

@[simp] theorem sourceWidth_word {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    sourceWidth cfg m .word = m+1 := rfl
@[simp] theorem sourceWidth_pivot {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) (j : Fin k) :
    sourceWidth cfg m (.pivot j.val) = (cfg.2 j.castSucc).length := by
  simp only [sourceWidth, dite_eq_left j.isLt]
  rfl
@[simp] theorem sourceWidth_anchor {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (b : Bool) :
    sourceWidth cfg m (.anchor j b) = 1 := rfl
@[simp] theorem sourceWidth_filler {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :
    sourceWidth cfg m .filler = (cfg.2 (Fin.last k)).length := rfl

abbrev SourceConstituent {k : ℕ} (cfg : SourceConfiguration k) (m : ℕ) :=
  (Template.schedule k 0).Constituent (sourceWidth cfg m)

def templateOriginalWord {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (x : SourceConstituent cfg m → PrimeUpTo Q) (side : Bool) : Fin (m+1) → PrimeUpTo Q :=
  fun i => x ⟨(.word,side),i⟩

def templateWordMask {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ) (J : ℤ)
    (x : SourceConstituent cfg m → PrimeUpTo Q) (side : Bool) : ℝ :=
  binIndicator J (templateOriginalWord cfg m x side)

theorem template_word_state {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (x : SourceConstituent cfg m → PrimeUpTo Q) (side : Bool) :
    constituentSampleState (schedule k 0) (sourceWidth cfg m) x (.word,side) =
      (characterTupleProduct (templateOriginalWord cfg m x side) : ℤ) := by
  simp only [constituentSampleState, characterTupleProduct, Nat.cast_prod]
  rfl

theorem templateWordMask_eq_state_bin {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ) (J : ℤ)
    (x : SourceConstituent cfg m → PrimeUpTo Q) (side : Bool) :
    templateWordMask cfg m J x side =
      if ⌊Real.log ((constituentSampleState (schedule k 0) (sourceWidth cfg m) x
        (.word,side) : ℤ) : ℝ)⌋ = J then 1 else 0 := by
  rw [template_word_state]
  simp only [Int.cast_natCast, log_characterTupleProduct]
  rfl

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI

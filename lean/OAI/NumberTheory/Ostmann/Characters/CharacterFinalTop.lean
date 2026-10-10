import OAI.NumberTheory.Ostmann.Characters.CharacterSelectedBulk
import OAI.NumberTheory.Ostmann.Construction.SelectedFinalPermutation

namespace OAI

/-! # The final character permutations leave the top label in each word fixed -/
namespace Ostmann
open scoped Classical

theorem characterTop_not_bulk {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f : ℕ) :
    characterTop m r f ∉ Set.range (characterBulk m r f) := by
  rintro ⟨i, hi⟩
  have h := congrArg (fun x : Σ v, Fin (characterSize m r f v) => x.2.val) hi
  change i.val + 1 = 0 at h
  omega

theorem character_final_top_fixed {k : ℕ} (m : ℕ) (r : Fin k → ℕ) (f n : ℕ)
    (e : FinalParityReassignments n m) (t : Fin (n + 1) → Bool) :
    let ρ := fun i : Σ v, Fin (characterSize m r f v) => characterRole k i.1
    let h := scheduledWordH ρ (n + 1) t ⟨characterTop m r f, characterTop_role m r f⟩
    selectedFinalPerm ρ n m (characterBulk m r f) (characterBulk_role m r f) e h = h := by
  intro ρ h
  apply selectedFinalPerm_fixed_of_origin
  change copyScheduleOrigin (n + 1) (copySchedulePath (n + 1) t (characterTop m r f)) ∉ _
  rw [copyScheduleOrigin_path]
  exact characterTop_not_bulk m r f

end Ostmann

end OAI

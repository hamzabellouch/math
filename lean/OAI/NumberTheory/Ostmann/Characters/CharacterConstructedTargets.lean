import OAI.NumberTheory.Ostmann.Characters.CharacterBackwardsWords

namespace OAI

/-! # One target function containing precisely the backwards pivot and filler data -/
namespace Ostmann

noncomputable def characterConstructedTargets (k : ℕ) (J logX B z m : ℝ)
    (a : Fin k × Bool → ℕ) : Option (Fin k) → ℝ :=
  let TP := characterPivotTarget k J (fun j => (a (j, false) : ℝ) + a (j, true))
    (fun j => characterPivotGap B z m j.val)
  fun j => j.elim
    (characterFillerTarget logX (characterBaseGap B z m) J TP (fun j b => (a (j, b) : ℝ))) TP

@[simp] theorem characterConstructedTargets_some (k : ℕ) (J logX B z m : ℝ)
    (a : Fin k × Bool → ℕ) (j : Fin k) :
    characterConstructedTargets k J logX B z m a (some j) =
      characterPivotTarget k J (fun j => (a (j, false) : ℝ) + a (j, true))
        (fun j => characterPivotGap B z m j.val) j := rfl

@[simp] theorem characterConstructedTargets_none (k : ℕ) (J logX B z m : ℝ)
    (a : Fin k × Bool → ℕ) :
    characterConstructedTargets k J logX B z m a none =
      characterFillerTarget logX (characterBaseGap B z m) J
        (characterPivotTarget k J (fun j => (a (j, false) : ℝ) + a (j, true))
          (fun j => characterPivotGap B z m j.val)) (fun j b => (a (j, b) : ℝ)) := rfl

end Ostmann

end OAI

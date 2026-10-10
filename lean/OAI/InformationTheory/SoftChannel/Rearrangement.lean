import OAI.InformationTheory.BooleanNoise.Rearrangement
import OAI.InformationTheory.SoftChannel.Wall

namespace OAI

section

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem Rearrangement_rearrangement_sign_bounds {F : Cube n → ℝ} (hF : IsSignValued F) :
    ∀ y, -1 ≤ F y ∧ F y ≤ 1 := by
  intro y
  rcases hF y with h | h <;> rw [h] <;> norm_num

end LeanBlast.CourtadeKumar
end
end

end OAI

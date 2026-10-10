import OAI.Combinatorics.Sensitivity.HammingBase
import OAI.Combinatorics.Sensitivity.Basic

namespace OAI

/-! The two-sided distance change under one raw-bit flip. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem nearestDistance_flip_le_add_one {I C : Type} [Fintype I] [Fintype C] [Nonempty C]
    (centers : C → I → Bool) (x : I → Bool) (i : I) :
    nearestDistance centers (flip x {i}) ≤ nearestDistance centers x + 1 := by
  simpa only [flip_flip] using nearestDistance_le_flip_add_one centers (flip x {i}) i

theorem nearestDistance_flip_abs_le_one {I C : Type} [Fintype I] [Fintype C] [Nonempty C]
    (centers : C → I → Bool) (x : I → Bool) (i : I) :
    |(nearestDistance centers x : ℤ) - nearestDistance centers (flip x {i})| ≤ 1 := by
  have h₁ := nearestDistance_le_flip_add_one centers x i
  have h₂ := nearestDistance_flip_le_add_one centers x i
  rw [abs_le]
  constructor <;> omega

end Paper320

end

end OAI

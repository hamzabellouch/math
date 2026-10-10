import OAI.Geometry.RCD.Coordinates.PatchAssembly

namespace OAI

/-! # A positive budget for finitely bounded scalar coefficients -/

namespace RegularPointCoordinates

/-- A common positive budget controls every coefficient below a fixed
bound, both absolutely and relative to the desired iteration tolerance. -/
theorem exists_uniform_patch_budget {P epsilon : ℝ} (hP : 0 ≤ P) (hepsilon : 0 < epsilon) :
    ∃ b : ℝ, 0 < b ∧ b ≤ epsilon ∧ b ≤ 1 / 8192 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ P → t * b ≤ min epsilon (1 / 8192) := by
  let s := min epsilon (1 / 8192)
  have hs : 0 < s := lt_min hepsilon (by norm_num)
  let b := s / (P + 1)
  have hb : 0 < b := div_pos hs (by positivity)
  have hbS : b ≤ s := div_le_self hs.le (by linarith)
  refine ⟨b, hb, hbS.trans (min_le_left _ _), hbS.trans (min_le_right _ _), ?_⟩
  intro t _ht htP
  calc
    t * b ≤ P * b := mul_le_mul_of_nonneg_right htP hb.le
    _ ≤ (P + 1) * b := mul_le_mul_of_nonneg_right (by linarith) hb.le
    _ = s := by dsimp only [b]; field_simp

end RegularPointCoordinates

end OAI

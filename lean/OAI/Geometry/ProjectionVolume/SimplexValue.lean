import OAI.Geometry.ProjectionVolume.SimplexBrightness
import OAI.Geometry.ProjectionVolume.SimplexZonotope
import OAI.Geometry.ProjectionVolume.ProjectionReconstruction
import OAI.Geometry.ProjectionVolume.ProductVolume

namespace OAI

open MeasureTheory

namespace Paper092

theorem standardSimplex_projectionBody (d : ℕ) (hd : 0 < d) :
    projectionBody (standardSimplex d) = simplexZonotope d := by
  apply projectionBody_eq_of_brightness_eq_support (simplexZonotope_isCompact d)
    (simplexZonotope_nonempty d) (simplexZonotope_convex d)
  intro u
  rw [standardSimplex_brightness d hd, simplexZonotope_support]

theorem standardSimplex_projectionBody_volume (d : ℕ) (hd : 0 < d) :
    (volume (projectionBody (standardSimplex d))).toReal =
      ((d : ℝ) + 1) / (((d - 1).factorial : ℝ) ^ d) := by
  rw [standardSimplex_projectionBody d hd, simplexZonotope_volume d hd]

theorem standardSimplex_normalizedProjectionVolume (d : ℕ) (hd : 0 < d) :
    normalizedProjectionVolume (standardSimplex d) = simplexConstant d := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  unfold normalizedProjectionVolume simplexConstant
  rw [standardSimplex_projectionBody_volume (n + 1) hd, standardSimplex_volume_real]
  simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
    div_pow, one_pow, pow_succ, mul_pow]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

end Paper092

end OAI

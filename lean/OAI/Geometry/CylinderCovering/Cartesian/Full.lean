import OAI.Geometry.CylinderCovering.Cartesian.FullDefinitions
import OAI.Geometry.CylinderCovering.Cartesian.Statement
import OAI.Geometry.CylinderCovering.Cartesian.Cover

namespace OAI

open Set
namespace CylinderCovering.CartesianCaps

theorem cutoff_essential : CartesianCutoffStatement := by
  intro τ η q hτ hη hq hq1
  have hη0 : 0 < η := hη.1
  obtain ⟨B, hB, htail⟩ := untruncated_contains_ray τ η q hτ.1 hη.1.le hq
  have hzero : (0 : ℝ) ∈ untruncated τ η q := by
    constructor
    · norm_num
    · simp only [mul_zero, height, D, zero_pow (by omega : 2 ≠ 0),
        zero_pow (by omega : 4 ≠ 0), zero_div, zero_add]
      positivity
  have hfar : B ∈ untruncated τ η q :=
    ⟨by linarith, htail B le_rfl⟩
  refine ⟨untruncated_not_bddAbove τ η q hτ.1 hη.1.le hq, ?_, B, hB, ?_⟩
  · intro hc
    have hone := hc.Icc_subset hzero hfar (show (1 : ℝ) ∈ Icc 0 B from ⟨by norm_num, hB⟩)
    exact untruncated_gap τ η q ⟨hτ.1.le,hτ.2⟩ hη.2 hq1 hone.2
  · intro s hs
    change B ≤ s at hs
    exact ⟨by linarith, htail s hs⟩

theorem cartesian_full : CartesianFullStatement :=
  ⟨cartesianAperture_proved, cartesian_cover, cutoff_essential⟩

end CylinderCovering.CartesianCaps

end OAI

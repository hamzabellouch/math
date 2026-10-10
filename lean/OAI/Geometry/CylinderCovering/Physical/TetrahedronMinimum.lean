import OAI.Geometry.CylinderCovering.Physical.Minimum

namespace OAI

noncomputable section
namespace RadialPhysical

theorem centered_modelBody_eq {b : ℝ} (hb : 0 < b) :
    modelBody true b = centeredTetrahedron b := by
  ext z
  constructor
  · rintro ⟨x, y, t, hx, hy, rfl⟩
    have hleft : 0 ≤ b * (1 + t) := (abs_nonneg x).trans hx
    have hright : 0 ≤ b * (1 - t) := (abs_nonneg y).trans hy
    have ht0 : -1 ≤ t := by nlinarith
    have ht1 : t ≤ 1 := by nlinarith
    exact ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩
  · rintro ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩
    exact ⟨x, y, t, hx, hy, rfl⟩

theorem physical_tetrahedron_minimum {b : ℝ} (hb : 0 < b) :
    CylinderCovering.minimumShadowArea (tetrahedron b) = b * height b := by
  change CylinderCovering.Similarity.minimumArea (tetrahedron b) = b * height b
  simpa [modelBody] using PhysicalMinimum.minimum_modelBody false hb

theorem centered_tetrahedron_minimum {b : ℝ} (hb : 0 < b) :
    CylinderCovering.minimumShadowArea (centeredTetrahedron b) = 4 * b * height b := by
  rw [← centered_modelBody_eq hb]
  exact PhysicalMinimum.minimum_modelBody true hb

end RadialPhysical

end

end OAI

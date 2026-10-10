import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
namespace CylinderCovering

theorem ruled_tetrahedron_eq_triangular :
    RuledApproximation.tetrahedron = TriangularCovering.K := by
  ext z
  constructor
  · rintro ⟨t, ht0, ht1, hx, hy, hz⟩
    refine ⟨z 0, z 1, t, ht0, ht1, hx, hy, ?_⟩
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hz
  · rintro ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩
    exact ⟨t, ht0, ht1, hx, hy, rfl⟩

theorem ruled_tetrahedron_minimum_shadow :
    minimumShadowArea RuledApproximation.tetrahedron = Real.sqrt 2 := by
  rw [ruled_tetrahedron_eq_triangular]
  exact TriangularCovering.projection_minimum

theorem ruled_tetrahedron_shadow_lower {u : Space} (hu : ‖u‖ = 1) :
    Real.sqrt 2 ≤ shadowArea RuledApproximation.tetrahedron u := by
  rw [ruled_tetrahedron_eq_triangular]
  exact TriangularCovering.shadowArea_ge_H hu

end CylinderCovering

end

end OAI

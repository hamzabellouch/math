import OAI.Geometry.CylinderCovering.Physical.Minimum

namespace OAI

namespace RadialPhysical.PhysicalMinimum

theorem minimum_edge_one_model : CylinderCovering.Similarity.minimumArea (modelBody false (1/2)) =
    Real.sqrt 2 / 4 := by
  rw [minimum_modelBody false (by norm_num : (0:ℝ) < 1/2)]
  simp only [Bool.false_eq_true, ite_false, height]
  ring

theorem minimum_unit_centered_model : CylinderCovering.Similarity.minimumArea (modelBody true 1) =
    4 * Real.sqrt 2 := by
  rw [minimum_modelBody true (by norm_num : (0:ℝ) < 1)]
  simp [height]

end RadialPhysical.PhysicalMinimum

end OAI

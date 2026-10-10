import OAI.Geometry.CylinderCovering.Nilpotent.Corollaries

namespace OAI

open Set MeasureTheory RuledApproximation CylinderCovering

theorem CylinderCovering.Nilpotent.zero_signed_sweep_finite_at_tolerance {ε : ℝ} (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' CylinderCovering.Nilpotent.signedSweep 0 0)
      (Real.sqrt 2 * (CylinderCovering.Nilpotent.I 0 + ε)) := by
  simpa using CylinderCovering.Nilpotent.signed_sweep_finite_at_tolerance
    (k := 0) (σ := 0) (by norm_num) (by norm_num) (by norm_num) hε

theorem CylinderCovering.Nilpotent.finite_counterexample_explicit_parameter : ∃ n : ℕ, ∃ C : Fin n → Cylinder,
    (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
    tetrahedron ⊆ familySet C ∧
    familyArea C < minimumShadowArea tetrahedron / 2 ∧
    relativeCost tetrahedron C < 1 / 2 := by
  exact CylinderCovering.Nilpotent.finite_counterexample_of_integral_saving
    (k := 1 / 3840) (by norm_num) (by norm_num)
    (CylinderCovering.Nilpotent.integral_lt_quarter (by norm_num) (by norm_num))

end OAI

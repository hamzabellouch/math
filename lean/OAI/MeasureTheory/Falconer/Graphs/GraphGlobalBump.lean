import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalChart

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceArcLength_pair_graph_plane_supported
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 < R)
    (hsupp : ∀ r u v, F r u v ≠ 0 → r/R ∈ Icc a b) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice a b z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          F (R*(‖η‖*Real.sqrt (1+z^2)/2))
            (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
            (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis)) := by
  have hz : ∀ r, r ∉ Icc (R*a) (R*b) →
      (∫ u, ∫ v, F r u v ∂sourceArcLength ∂sourceArcLength) = 0 := by
    intro r hr
    have he : ∀ u v, F r u v = 0 := by
      intro u v
      by_contra hn
      have hh := hsupp r u v hn
      apply hr
      exact ⟨by nlinarith [(le_div_iff₀ hR).mp hh.1],
        by nlinarith [(div_le_iff₀ hR).mp hh.2]⟩
    simp only [he, integral_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hR.le)]
  exact sourceArcLength_pair_graph_plane_normalized hF ha hab hR axis

theorem sourceArcLength_pair_graph_plane_bump
    {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {R : ℝ} (hR : 0 < R) (axis : ℝ) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • F r u v ∂sourceArcLength ∂sourceArcLength) =
      ∫ z : ℝ, ∫ η in graphGlobalSlice (1/4) 4 z,
        (‖η‖*Real.sqrt (1+z^2))⁻¹ •
          (Ψ (‖η‖*Real.sqrt (1+z^2)/2) •
            F (R*(‖η‖*Real.sqrt (1+z^2)/2))
              (sourceUnitDirection (graphPlaneAngle η+Real.arctan z))
              (sourceUnitDirection (graphPlaneAngle η-Real.arctan z+axis))) := by
  have hc : Continuous (fun p : ℝ × (UnitCircle × UnitCircle) =>
      Ψ (p.1/R) • F p.1 p.2.1 p.2.2) :=
    (hΨ.comp (continuous_fst.div_const R)).smul hF
  have hb : ∀ r u v, Ψ (r/R) • F r u v ≠ 0 → r/R ∈ Icc (1/4:ℝ) 4 := by
    intro r u v h
    have hn : Ψ (r/R) ≠ 0 := by intro he; exact h (by rw [he, zero_smul])
    exact Ioo_subset_Icc_self (hsupp (r/R) hn)
  have he := sourceArcLength_pair_graph_plane_supported hc
    (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) ≤ 4) hR hb axis
  simpa only [mul_div_cancel_left₀ _ hR.ne'] using he

end PlanarFalconer

end OAI

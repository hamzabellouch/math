import OAI.Geometry.SurfaceImmersion.Atlas.TransverseCutoff

namespace OAI

/-! A transverse cutoff of a first-order flat remainder tends to zero
in C1, even though the cutoff derivative grows as its support narrows. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem flat_transverse_cutoff_bound : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (R : Base → ProjectionTarget 3), ContDiff ℝ ∞ R →
      (∀ t, R (crosscapAxis t) = 0) → (∀ t, fderiv ℝ R (crosscapAxis t) = 0) →
      ∀ ρ C : ℝ, 0 ≤ C →
      (∀ x ∈ closedBall (0 : Base) ρ, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ C) →
      ∀ r : ℝ, 0 < r → ∀ x ∈ closedBall (0 : Base) ρ,
        ‖transverseCutoff r x • R x‖ ≤ C*r^2 ∧
        ‖fderiv ℝ (fun y => transverseCutoff r y • R y) x‖ ≤ (B+1)*C*r := by
  obtain ⟨B,hB,hcut⟩ := transverseCutoff_derivative_bound
  refine ⟨B,hB,?_⟩
  intro R hR h0 hD0 ρ C hC hb r hr x hx
  by_cases hxs : x ∈ tsupport (transverseCutoff r)
  · have hxr : |x 0| ≤ r := transverseCutoff_tsupport hr hxs
    have hv : ‖R x‖ ≤ C*r^2 := (axis_flat_value_bound hR h0 hD0 hC hb hx).trans
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ (abs_nonneg _) hr.le |>.mpr hxr) hC)
    have hd : ‖fderiv ℝ R x‖ ≤ C*r := (axis_flat_first_bound hR hD0 hb hx).trans
      (mul_le_mul_of_nonneg_left hxr hC)
    have hprod := ((transverseCutoff_smooth r).differentiable (by simp) x).hasFDerivAt.smul
      (hR.differentiable (by simp) x).hasFDerivAt
    change HasFDerivAt (fun y => transverseCutoff r y • R y) _ x at hprod
    constructor
    · rw [norm_smul,Real.norm_eq_abs]
      calc
        _ ≤ 1*(C*r^2) := mul_le_mul (transverseCutoff_le_one r x) hv (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    · rw [hprod.fderiv]
      calc
        _ ≤ ‖transverseCutoff r x • fderiv ℝ R x‖ +
            ‖(fderiv ℝ (transverseCutoff r) x).smulRight (R x)‖ := norm_add_le _ _
        _ = |transverseCutoff r x| * ‖fderiv ℝ R x‖ +
            ‖fderiv ℝ (transverseCutoff r) x‖*‖R x‖ := by
              rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ 1*(C*r) + (B/r)*(C*r^2) := add_le_add
            (mul_le_mul (transverseCutoff_le_one r x) hd (norm_nonneg _) (by norm_num))
            (mul_le_mul (hcut r hr x) hv (norm_nonneg _) (div_nonneg hB hr.le))
        _ = (B+1)*C*r := by field_simp; ring
  · have he : (fun y => transverseCutoff r y • R y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
      simp [hy]
    constructor
    · have hex : transverseCutoff r x • R x = 0 := he.self_of_nhds
      rw [hex,norm_zero]
      positivity
    · rw [he.fderiv_eq]
      simpa using (mul_nonneg (mul_nonneg (by linarith : 0 ≤ B+1) hC) hr.le)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

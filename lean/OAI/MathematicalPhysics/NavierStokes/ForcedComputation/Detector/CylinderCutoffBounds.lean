import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderCutoffLimit

namespace OAI

/-! A common constant for the first and second derivatives of the
horizontal energy cutoffs. Their boundary terms decay as the radius grows. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector PlanarHamiltonian Set Filter
open scoped ContDiff Topology

private def baseEnergyCutoff (x : Plane) : ℝ := massCutoff x ^ 2

private theorem baseEnergyCutoff_smooth : ContDiff ℝ ∞ baseEnergyCutoff :=
  massCutoff_smooth.pow 2

private theorem baseEnergyCutoff_support : HasCompactSupport baseEnergyCutoff := by
  have he : baseEnergyCutoff = massCutoff * massCutoff := by
    funext x
    simp only [baseEnergyCutoff, pow_two, Pi.mul_apply]
  rw [he]
  exact massCutoff_compactSupport.mul_right

theorem cylinderWeight_smooth (n : ℕ) : ContDiff ℝ ∞ (cylinderWeight n) :=
  (concentrationCutoff_smooth ((n : ℝ) + 1) 0).pow 2

theorem cylinderWeight_derivative_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Plane),
      ‖fderiv ℝ (cylinderWeight n) x‖ ≤ C * ((n : ℝ) + 1)⁻¹ ∧
      |scalarLaplacian (cylinderWeight n) x| ≤ C * ((n : ℝ) + 1)⁻¹ ^ 2 := by
  have hdc := (baseEnergyCutoff_smooth.fderiv_right (m := ∞) (by simp)).continuous
  obtain ⟨A, hA⟩ := hdc.bounded_above_of_compact_support (baseEnergyCutoff_support.fderiv ℝ)
  have hlc := (ExpandingDetector.scalarLaplacian_smooth baseEnergyCutoff_smooth).continuous
  obtain ⟨B, hB⟩ := hlc.bounded_above_of_compact_support
    (scalarLaplacian_compactSupport baseEnergyCutoff_support)
  let C := max 0 (max A B)
  have hAC : A ≤ C := (le_max_left A B).trans (le_max_right _ _)
  have hBC : B ≤ C := (le_max_right A B).trans (le_max_right _ _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro n x
  have hμ : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have he : cylinderWeight n = fun y =>
      baseEnergyCutoff (scalarAffineScale ((n : ℝ) + 1)⁻¹ 0 y) := rfl
  constructor
  · rw [he]
    have hd := (baseEnergyCutoff_smooth.differentiable (by simp) _).hasFDerivAt.comp x
      (scalarAffineScale_hasFDerivAt ((n : ℝ) + 1)⁻¹ 0 x)
    change HasFDerivAt (fun y => baseEnergyCutoff (scalarAffineScale ((n : ℝ)+1)⁻¹ 0 y)) _ x
      at hd
    rw [hd.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (le_max_left _ _) hμ)
    intro v
    rw [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hμ]
    calc
      ((n : ℝ) + 1)⁻¹ * ‖fderiv ℝ baseEnergyCutoff
          (scalarAffineScale ((n : ℝ) + 1)⁻¹ 0 x) v‖
          ≤ ((n : ℝ) + 1)⁻¹ * (C * ‖v‖) := by
        apply mul_le_mul_of_nonneg_left _ hμ
        exact ((fderiv ℝ baseEnergyCutoff _).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right ((hA _).trans hAC) (norm_nonneg v))
      _ = _ := by ring
  · rw [he, scalarLaplacian_affine_scale baseEnergyCutoff_smooth,
      abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      ((n : ℝ) + 1)⁻¹ ^ 2 * |scalarLaplacian baseEnergyCutoff
          (scalarAffineScale ((n : ℝ) + 1)⁻¹ 0 x)|
          ≤ ((n : ℝ) + 1)⁻¹ ^ 2 * C := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [Real.norm_eq_abs] using (hB _).trans hBC
      _ = _ := mul_comm _ _

end ForcedComputation.VelocityDetector

end

end OAI

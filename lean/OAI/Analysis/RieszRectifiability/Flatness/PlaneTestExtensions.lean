import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedRegionTests
import OAI.Analysis.RieszRectifiability.Rigidity.PlaneHeightDistribution
import OAI.Analysis.RieszRectifiability.Kernel.DerivativeTests

namespace OAI

/-!
# Compact ambient extensions of plane tests

An adjoint coordinate projection extends a test function from an affine plane.
A radial cutoff makes the extension compactly supported while retaining its
values on the plane and explicit uniform and Lipschitz bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Function SchwartzMap
open scoped NNReal ContDiff

theorem exists_compact_ambient_plane_test {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (g : Ambient n → ℝ)
    (hc : HasCompactSupport g) (K B : ℝ≥0) (hg : LipschitzWith K g)
    (hB : ∀ u, |g u| ≤ (B : ℝ)) :
    ∃ (φ : Ambient d → ℝ) (J : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith J φ ∧ (∀ x, |φ x| ≤ (B : ℝ)) ∧
      (∀ u, φ (a + L u) = g u) ∧
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) ∧
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = ∫ u, g u := by
  obtain ⟨R, _, hR⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Ambient n)
  let π : Ambient d → Ambient n := fun x => L.toContinuousLinearMap.adjoint (x - a)
  have hπ : LipschitzWith ‖L.toContinuousLinearMap.adjoint‖₊ π := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using!
      L.toContinuousLinearMap.adjoint.lipschitzWith.dist_le_mul (x - a) (y - a)
  have hleft : ∀ u, π (a + L u) = u := by
    intro u
    change L.toContinuousLinearMap.adjoint ((a + L u) - a) = u
    rw [add_sub_cancel_left]
    exact DFunLike.congr_fun L.adjoint_comp_self u
  let χ := radialUnitCutoff a R
  let φ : Ambient d → ℝ := fun x => χ x * g (π x)
  have hχ : LipschitzWith 1 χ := radialUnitCutoff_lipschitz a R
  have hχB : ∀ x, |χ x| ≤ (1 : ℝ≥0) := by
    intro x
    rw [abs_of_nonneg (radialUnitCutoff_bounds a R x).1]
    exact (radialUnitCutoff_bounds a R x).2
  have hφ : LipschitzWith (1 * (K * ‖L.toContinuousLinearMap.adjoint‖₊) + 1 * B) φ :=
    lipschitz_bounded_product_real hχ (hg.comp hπ) hχB (fun x => hB (π x))
  have hext : ∀ u, φ (a + L u) = g u := by
    intro u
    change χ (a + L u) * g (π (a + L u)) = g u
    rw [hleft]
    by_cases hu : g u = 0
    · rw [hu, mul_zero]
    have hnorm : ‖u‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using! hR (subset_tsupport g hu)
    have hχone : χ (a + L u) = 1 := by
      apply radialUnitCutoff_eq_one
      simpa only [dist_eq_norm, add_sub_cancel_left, L.norm_map] using! hnorm
    rw [hχone, one_mul]
  refine ⟨φ, _, (radialUnitCutoff_hasCompactSupport a R).mul_right, hφ, ?_, hext, ?_, ?_⟩
  · intro x
    calc
      |φ x| = |χ x| * |g (π x)| := abs_mul _ _
      _ ≤ 1 * (B : ℝ) := mul_le_mul (hχB x) (hB (π x)) (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · rw [coordinatePlaneMeasure_affine_eq_map]
    apply (integrable_map_measure (μ := (volume : Measure (Ambient n))) hφ.continuous.aestronglyMeasurable
      (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))).mpr
    have hIg : Integrable g (volume : Measure (Ambient n)) :=
      hg.continuous.integrable_of_hasCompactSupport hc
    simpa only [Function.comp_def, hext] using! hIg
  · rw [coordinatePlaneMeasure_affine_eq_map,
      integral_map (show AEMeasurable (fun u : Ambient n => a + L u) volume from (by fun_prop))
        hφ.continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall hext)

theorem exists_compact_ambient_directional_test {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (g : Ambient n → ℝ)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g) (v : Ambient n) :
    ∃ (φ : Ambient d → ℝ) (J B : ℝ≥0),
      HasCompactSupport φ ∧ LipschitzWith J φ ∧ (∀ x, |φ x| ≤ (B : ℝ)) ∧
      (∀ u, φ (a + L u) = fderiv ℝ g u v) ∧
      Integrable φ (coordinatePlaneMeasure (affinePlaneSection a L)) ∧
      (∫ x, φ x ∂coordinatePlaneMeasure (affinePlaneSection a L)) = 0 := by
  obtain ⟨K, B, hcompact, hLip, hbound, _, hzero⟩ :=
    compact_smooth_directional_test_admissible g hc hg v
  obtain ⟨φ, J, hcφ, hφ, hBφ, hext, hI, hmean⟩ :=
    exists_compact_ambient_plane_test a L (fun u => fderiv ℝ g u v) hcompact K B hLip hbound
  exact ⟨φ, J, B, hcφ, hφ, hBφ, hext, hI, hmean.trans hzero⟩

end

end RieszRectifiability

end OAI

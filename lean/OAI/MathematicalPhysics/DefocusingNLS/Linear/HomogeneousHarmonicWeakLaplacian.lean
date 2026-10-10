import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousClassicalGreen
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTestSupport
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolarL2

namespace OAI

/-! # The angular projection of the classical Laplacian, in weak radial form

The only angular assumptions are the explicit degree-zero homogeneity and
spherical Laplacian eigenfunction identities. The function being projected
is an arbitrary C² Cartesian function.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff SchwartzMap Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def harmonicAngularCoefficient (Y F : E → ℂ) (r : ℝ) : ℂ :=
  ∫ z : PhysicalUnitSphere, Y z.1 * F (r • z.1) ∂physicalSphereMeasure

private theorem integral_eq_polar_iterated (G : E → ℂ) (hG : Integrable G) :
    (∫ x : E, G x) = ∫ r : PhysicalPositiveRadius,
      (∫ z : PhysicalUnitSphere, G (r.1 • z.1) ∂physicalSphereMeasure)
        ∂physicalRadiusMeasure := by
  have hm : AEStronglyMeasurable G
      (Measure.map physicalPolarPoint physicalPolarMeasure) := by
    rw [measurePreserving_physicalPolarPoint.map_eq]
    exact hG.aestronglyMeasurable
  have he := integral_map measurePreserving_physicalPolarPoint.measurable.aemeasurable hm
  rw [measurePreserving_physicalPolarPoint.map_eq] at he
  rw [he]
  exact integral_prod_symm _
    (measurePreserving_physicalPolarPoint.integrable_comp_of_integrable hG)

/-- The weak radial Laplacian identity in dimension twelve. Squared-radius
tests suffice locally, and avoid any artificial derivative at the origin. -/
theorem harmonicAngularCoefficient_weak_laplacian
    (Y F : E → ℂ) (lam : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(lam / (‖x‖ ^ 2 : ℝ)) * Y x)
    (hF : ContDiff ℝ 2 F)
    (ψ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    (∫ r : PhysicalPositiveRadius, ψ (r.1 ^ 2) *
      harmonicAngularCoefficient Y (Δ F) r ∂physicalRadiusMeasure) =
    ∫ r : PhysicalPositiveRadius,
      (((4 * r.1 ^ 2 : ℝ) : ℂ) * deriv (deriv ψ) (r.1 ^ 2) +
        24 * deriv ψ (r.1 ^ 2) - lam / (r.1 ^ 2 : ℝ) * ψ (r.1 ^ 2)) *
      harmonicAngularCoefficient Y F r ∂physicalRadiusMeasure := by
  let T : 𝓢(E, ℂ) := squaredHarmonicSchwartz ψ Y hc hs hY
  have hT : HasCompactSupport T := squaredHarmonicTest_hasCompactSupport ψ hc Y
  have hiL : Integrable (fun x : E => T x * Δ F x) :=
    (T.continuous.mul (continuous_laplacian_of_contDiff_two F hF)).integrable_of_hasCompactSupport
      hT.mul_right
  have hiR : Integrable (fun x : E => Δ (fun y => T y) x * F x) :=
    ((continuous_laplacian_of_contDiff_two T (T.smooth 2)).mul hF.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian T hT).mul_right
  have hn (r : PhysicalPositiveRadius) (z : PhysicalUnitSphere) : ‖r.1 • z.1‖ = r.1 := by
    have hz : ‖z.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2, hz, mul_one]
  have hleft (r : PhysicalPositiveRadius) :
      (∫ z : PhysicalUnitSphere, T (r.1 • z.1) * Δ F (r.1 • z.1) ∂physicalSphereMeasure) =
        ψ (r.1 ^ 2) * harmonicAngularCoefficient Y (Δ F) r := by
    rw [harmonicAngularCoefficient, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    change ψ (‖r.1 • z.1‖ ^ 2) * Y (r.1 • z.1) * Δ F (r.1 • z.1) = _
    rw [hn, hRay z.1 r.1 r.2, mul_assoc]
  have hright (r : PhysicalPositiveRadius) :
      (∫ z : PhysicalUnitSphere, Δ (fun y => T y) (r.1 • z.1) * F (r.1 • z.1)
        ∂physicalSphereMeasure) =
      (((4 * r.1 ^ 2 : ℝ) : ℂ) * deriv (deriv ψ) (r.1 ^ 2) +
        24 * deriv ψ (r.1 ^ 2) - lam / (r.1 ^ 2 : ℝ) * ψ (r.1 ^ 2)) *
        harmonicAngularCoefficient Y F r := by
    rw [harmonicAngularCoefficient, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    have hx : r.1 • z.1 ≠ 0 := by
      intro hz
      have := hn r z
      rw [hz, norm_zero] at this
      exact r.2.ne' this.symm
    change Δ (fun y : E => ψ (‖y‖ ^ 2) * Y y) (r.1 • z.1) * F (r.1 • z.1) = _
    rw [radialSquare_harmonic_test_laplacian ψ Y _ lam (ψ.smooth 2).contDiffAt
      ((hY _ hx).of_le (by simp))
      (zero_euler_of_ray_constant Y _ ((hY _ hx).differentiableAt (by simp))
        (hRay _)) (hEigen _ hx), hn, hRay z.1 r.1 r.2, mul_assoc]
  calc
    _ = ∫ x : E, T x * Δ F x := by
      rw [integral_eq_polar_iterated _ hiL]
      exact integral_congr_ae (Eventually.of_forall fun r => (hleft r).symm)
    _ = ∫ x : E, Δ (fun y => T y) x * F x := compactTest_laplacian_green T hT F hF
    _ = _ := by
      rw [integral_eq_polar_iterated _ hiR]
      exact integral_congr_ae (Eventually.of_forall hright)

end DefocusingNLS

end OAI

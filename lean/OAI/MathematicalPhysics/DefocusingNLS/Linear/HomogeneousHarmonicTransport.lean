import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicRadialEquation

namespace OAI

/-! # Angular averaging of radial transport and multiplication

These identities use the actual physical realization. They complement the
radial Laplacian identity with the other terms of the linearized generator.
-/

open MeasureTheory Set Filter
open scoped ContDiff SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem continuous_harmonicSphere (Y : E → ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x) :
    Continuous (fun z : PhysicalUnitSphere => Y z.1) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hz : z.1 ≠ 0 := by
    have hn : ‖z.1‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.2
    intro he
    simp [he] at hn
  exact (hY z.1 hz).continuousAt.comp continuous_subtype_val.continuousAt

theorem memLp_star_harmonicSphere (Y : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) :
    MemLp (fun z : PhysicalUnitSphere => star (Y z.1)) 2 physicalSphereMeasure := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hY.star.continuousOn
  exact MemLp.of_bound hY.star.aestronglyMeasurable B
    (Eventually.of_forall fun z => hB z (mem_univ z))

theorem homogeneous_harmonic_projection (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (Y : E → ℂ) :
    homogeneousAngularProjection a k ha ha1 hk (fun z => star (Y z.1)) u =
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x) := by
  funext r
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [RCLike.inner_apply', starRingEnd_apply, star_star]

theorem homogeneous_harmonic_contDiff (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (Y : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) :
    ContDiff ℝ 2 (harmonicAngularCoefficient Y
      (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x)) := by
  rw [← homogeneous_harmonic_projection a k ha ha1 hk u Y]
  exact contDiff_homogeneousAngularProjection a k ha ha1 hk _
    (memLp_star_harmonicSphere Y hY) u

theorem homogeneous_harmonic_smul (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (Y : E → ℂ)
    (c : ℂ) (r : ℝ) :
    harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk (c • u) x) r =
      c * harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x) r := by
  rw [harmonicAngularCoefficient, harmonicAngularCoefficient, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [map_smul, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem homogeneous_harmonic_deriv (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (Y : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) (r : ℝ) :
    deriv (harmonicAngularCoefficient Y
      (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x)) r =
    ∫ z : PhysicalUnitSphere, Y z.1 *
      fderiv ℝ (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x) (r • z.1) z.1
      ∂physicalSphereMeasure := by
  rw [← homogeneous_harmonic_projection a k ha ha1 hk u Y]
  have hd := (hasDerivAt_homogeneousAngularProjection a k ha ha1 hk
    (fun z => star (Y z.1)) (memLp_star_harmonicSphere Y hY) u r).deriv
  simpa only [RCLike.inner_apply', starRingEnd_apply, star_star] using hd

theorem homogeneous_harmonic_euler (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (Y : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) (r : ℝ) :
    harmonicAngularCoefficient Y
      (fun x => fderiv ℝ (fun y => homogeneousPhysicalCLM a k ha ha1 hk u y) x x) r =
    (r : ℂ) * deriv (harmonicAngularCoefficient Y
      (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x)) r := by
  rw [homogeneous_harmonic_deriv a k ha ha1 hk u Y hY r, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [map_smul, Complex.real_smul]
  ring

theorem harmonicAngularCoefficient_radial_mul (Y F : E → ℂ) (c : ℝ → ℂ)
    (r : ℝ) (hr : 0 < r) :
    harmonicAngularCoefficient Y (fun x => c ‖x‖ * F x) r =
      c r * harmonicAngularCoefficient Y F r := by
  rw [harmonicAngularCoefficient, harmonicAngularCoefficient, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : ‖z.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
  ring

theorem integrable_harmonicSphere_product (Y F : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) (hF : Continuous F) (r : ℝ) :
    Integrable (fun z : PhysicalUnitSphere => Y z.1 * F (r • z.1)) physicalSphereMeasure := by
  have hc : Continuous (fun z : PhysicalUnitSphere => Y z.1 * F (r • z.1)) :=
    hY.mul (hF.comp (by fun_prop : Continuous (fun z : PhysicalUnitSphere => r • z.1)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem harmonicAngularCoefficient_four (Y F₁ F₂ F₃ F₄ : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1))
    (h₁ : Continuous F₁) (h₂ : Continuous F₂) (h₃ : Continuous F₃) (h₄ : Continuous F₄)
    (c₁ c₂ c₃ c₄ : ℂ) (r : ℝ) :
    harmonicAngularCoefficient Y
      (fun x => c₁ * F₁ x + c₂ * F₂ x + c₃ * F₃ x + c₄ * F₄ x) r =
      c₁ * harmonicAngularCoefficient Y F₁ r + c₂ * harmonicAngularCoefficient Y F₂ r +
      c₃ * harmonicAngularCoefficient Y F₃ r + c₄ * harmonicAngularCoefficient Y F₄ r := by
  have hi₁ := (integrable_harmonicSphere_product Y F₁ hY h₁ r).const_mul c₁
  have hi₂ := (integrable_harmonicSphere_product Y F₂ hY h₂ r).const_mul c₂
  have hi₃ := (integrable_harmonicSphere_product Y F₃ hY h₃ r).const_mul c₃
  have hi₄ := (integrable_harmonicSphere_product Y F₄ hY h₄ r).const_mul c₄
  change (∫ z : PhysicalUnitSphere, Y z.1 *
    (c₁ * F₁ (r • z.1) + c₂ * F₂ (r • z.1) + c₃ * F₃ (r • z.1) + c₄ * F₄ (r • z.1))
    ∂physicalSphereMeasure) = _
  calc
    _ = ∫ z : PhysicalUnitSphere,
        c₁ * (Y z.1 * F₁ (r • z.1)) + c₂ * (Y z.1 * F₂ (r • z.1)) +
        c₃ * (Y z.1 * F₃ (r • z.1)) + c₄ * (Y z.1 * F₄ (r • z.1))
        ∂physicalSphereMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = _ := by
      have hsum₄ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
      have hsum₃ := integral_add (hi₁.add hi₂) hi₃
      have hsum₂ := integral_add hi₁ hi₂
      simp only [Pi.add_apply] at hsum₄ hsum₃ hsum₂
      rw [hsum₄, hsum₃, hsum₂]
      simp only [integral_const_mul, harmonicAngularCoefficient]

end DefocusingNLS

end OAI

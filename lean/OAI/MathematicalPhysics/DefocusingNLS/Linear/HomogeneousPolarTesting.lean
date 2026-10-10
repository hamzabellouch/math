import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialComplexTesting

namespace OAI

/-! # Integrable polar tests of the faithful physical realization

The radial variable here is ordinary Lebesgue measure on the real line.
This lets a compactly supported radial test absorb the polar Jacobian before
integration by parts. The test is a bounded functional on physical C0.
-/

open MeasureTheory Set
open scoped ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalLinePolarMeasure : Measure (PhysicalUnitSphere × ℝ) :=
  physicalSphereMeasure.prod volume

private theorem physicalCZero_norm_le (f : C₀(E, ℂ)) (x : E) : ‖f x‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_coe_le_norm f.toBCF x).trans_eq
    ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

private theorem integrable_linePolarTest (K : PhysicalUnitSphere × ℝ → ℂ)
    (hK : Integrable K physicalLinePolarMeasure) (f : C₀(E, ℂ)) :
    Integrable (fun p : PhysicalUnitSphere × ℝ => K p * f (p.2 • p.1.1))
      physicalLinePolarMeasure := by
  apply (hK.norm.mul_const ‖f‖).mono'
    (hK.aestronglyMeasurable.mul
      (f.continuous.comp (continuous_snd.smul continuous_fst.subtype_val)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖K p * f (p.2 • p.1.1)‖ ≤ ‖K p‖ * ‖f‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (physicalCZero_norm_le f _) (norm_nonneg _)

/-- An L¹ polar test is continuous on the actual physical C0 realization. -/
noncomputable def physicalPolarTest (K : PhysicalUnitSphere × ℝ → ℂ)
    (hK : Integrable K physicalLinePolarMeasure) : C₀(E, ℂ) →L[ℂ] ℂ := by
  let L : C₀(E, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ p, K p * f (p.2 • p.1.1) ∂physicalLinePolarMeasure
      map_add' := by
        intro f g
        simp only [ZeroAtInftyContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_linePolarTest K hK f) (integrable_linePolarTest K hK g)
      map_smul' := by
        intro c f
        change (∫ p, K p * (c * f (p.2 • p.1.1)) ∂physicalLinePolarMeasure) =
          c * ∫ p, K p * f (p.2 • p.1.1) ∂physicalLinePolarMeasure
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with p
        ring }
  refine L.mkContinuous (∫ p, ‖K p‖ ∂physicalLinePolarMeasure) ?_
  intro f
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ p, ‖K p * f (p.2 • p.1.1)‖ ∂physicalLinePolarMeasure) ≤
        ∫ p, ‖K p‖ * ‖f‖ ∂physicalLinePolarMeasure := by
      apply integral_mono (integrable_linePolarTest K hK f).norm (hK.norm.mul_const ‖f‖)
      intro p
      change ‖K p * f (p.2 • p.1.1)‖ ≤ ‖K p‖ * ‖f‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (physicalCZero_norm_le f _) (norm_nonneg _)
    _ = (∫ p, ‖K p‖ ∂physicalLinePolarMeasure) * ‖f‖ := integral_mul_const _ _

@[simp] theorem physicalPolarTest_apply (K : PhysicalUnitSphere × ℝ → ℂ)
    (hK : Integrable K physicalLinePolarMeasure) (f : C₀(E, ℂ)) :
    physicalPolarTest K hK f =
      ∫ p, K p * f (p.2 • p.1.1) ∂physicalLinePolarMeasure := rfl

/-- Product tests are integrable without regularity of the angular factor. -/
theorem integrable_linePolarProduct (h : PhysicalUnitSphere → ℂ) (φ : ℝ → ℂ)
    (hh : Integrable h physicalSphereMeasure) (hφ : Integrable φ) :
    Integrable (fun p : PhysicalUnitSphere × ℝ => star (h p.1) * φ p.2)
      physicalLinePolarMeasure := by
  have hs : Integrable (fun ω => star (h ω)) physicalSphereMeasure := by
    apply hh.norm.mono' hh.aestronglyMeasurable.star
    filter_upwards [] with ω
    change ‖star (h ω)‖ ≤ ‖h ω‖
    exact le_of_eq (norm_star _)
  exact hs.mul_prod hφ

/-- The product-test functional equals its iterated angular/radial formula. -/
theorem physicalPolarTest_product (h : PhysicalUnitSphere → ℂ) (φ : ℝ → ℂ)
    (hh : Integrable h physicalSphereMeasure) (hφ : Integrable φ)
    (f : C₀(E, ℂ)) :
    physicalPolarTest (fun p => star (h p.1) * φ p.2)
        (integrable_linePolarProduct h φ hh hφ) f =
      ∫ ω, star (h ω) * (∫ r, φ r * f (r • ω.1)) ∂physicalSphereMeasure := by
  rw [physicalPolarTest_apply]
  change (∫ p, star (h p.1) * φ p.2 * f (p.2 • p.1.1)
    ∂physicalSphereMeasure.prod volume) = _
  trans ∫ ω, ∫ r, star (h ω) * φ r * f (r • ω.1) ∂volume ∂physicalSphereMeasure
  · exact integral_prod _ (integrable_linePolarTest _ (integrable_linePolarProduct h φ hh hφ) f)
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [mul_assoc, integral_const_mul]

end DefocusingNLS

end OAI

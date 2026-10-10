import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicTransport
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicCompleteness

namespace OAI

/-! # Linear harmonic observations and their separating property -/

open Set MeasureTheory

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousHarmonicMoment (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (Y : E → ℂ) (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) (r : ℝ) :
    HomogeneousY a k →ₗ[ℂ] ℂ where
  toFun u := harmonicAngularCoefficient Y (homogeneousPhysicalCLM a k ha ha1 hk u) r
  map_add' u v := by
    change (∫ z : PhysicalUnitSphere, Y z.1 *
      (homogeneousPhysicalCLM a k ha ha1 hk (u + v)) (r • z.1) ∂physicalSphereMeasure) = _
    simp only [map_add, ZeroAtInftyContinuousMap.add_apply, mul_add]
    exact integral_add
      (integrable_harmonicSphere_product Y _ hY
        (homogeneousPhysicalCLM a k ha ha1 hk u).continuous r)
      (integrable_harmonicSphere_product Y _ hY
        (homogeneousPhysicalCLM a k ha ha1 hk v).continuous r)
  map_smul' c u := homogeneous_harmonic_smul a k ha ha1 hk u Y c r

noncomputable def homogeneousPairHarmonicMoment (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (Y : E → ℂ) (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1))
    (first : Bool) (r : ℝ) : (HomogeneousY a k × HomogeneousY a k) →ₗ[ℂ] ℂ :=
  (homogeneousHarmonicMoment a k ha ha1 hk Y hY r).comp
    (if first then LinearMap.fst ℂ _ _ else LinearMap.snd ℂ _ _)

theorem physical_zero_of_harmonic_coefficients (F : E → ℂ) (hF : Continuous F)
    (h : ∀ (p : PhysicalRealPolynomial) (ell : ℕ), p.IsHomogeneous ell →
      physicalPolynomialLaplacian p = 0 → ∀ r : ℝ, 0 < r →
        harmonicAngularCoefficient (physicalHarmonicExtension p ell) F r = 0) : F = 0 := by
  by_contra hne
  obtain ⟨p, ell, r, hp, hDp, hr, hm⟩ := physical_exists_nonzero_harmonic_coefficient F hF hne
  exact hm (h p ell hp hDp r hr)

end DefocusingNLS

end OAI

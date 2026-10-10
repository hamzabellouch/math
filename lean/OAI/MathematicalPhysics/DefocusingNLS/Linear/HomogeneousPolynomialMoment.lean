import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicFunctional
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalLowDegreeMoments

namespace OAI

/-! # Polynomial linearity of a fixed-radius homogeneous observation -/

open MeasureTheory

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPairSphereFunction (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (first : Bool) (r : ℝ) (u : HomogeneousY a k × HomogeneousY a k) :
    C(PhysicalUnitSphere, ℂ) :=
  ⟨fun z => homogeneousPhysicalCLM a k ha ha1 hk (if first then u.1 else u.2) (r • z.1),
    (homogeneousPhysicalCLM a k ha ha1 hk (if first then u.1 else u.2)).continuous.comp
      (by fun_prop)⟩

theorem homogeneousPairHarmonicMoment_eq_sphere (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (p : PhysicalRealPolynomial) (ell : ℕ) (first : Bool) (r : ℝ)
    (u : HomogeneousY a k × HomogeneousY a k) :
    homogeneousPairHarmonicMoment a k ha ha1 hk (physicalHarmonicExtension p ell)
      (continuous_harmonicSphere _ (physicalHarmonicExtension_contDiffAt p ell)) first r u =
      physicalSphereMoment (homogeneousPairSphereFunction a k ha ha1 hk first r u)
        (physicalSpherePolynomial p) := by
  cases first <;>
    change (∫ z : PhysicalUnitSphere, physicalHarmonicExtension p ell z.1 * _ ∂physicalSphereMeasure) = _ <;>
    simp only [physicalHarmonicExtension_sphere] <;> rfl

theorem homogeneousPairPolynomialMoment_complete (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ell : ℕ)
    {J : Type*} (p : J → PhysicalRealPolynomial)
    (hspan : ∀ L : PhysicalRealPolynomial →ₗ[ℝ] ℂ, (∀ j, L (p j) = 0) →
      ∀ q : PhysicalRealPolynomial, q.IsHomogeneous ell → L q = 0)
    (first : Bool) (r : ℝ) (u : HomogeneousY a k × HomogeneousY a k)
    (hu : ∀ j, homogeneousPairHarmonicMoment a k ha ha1 hk (physicalHarmonicExtension (p j) ell)
      (continuous_harmonicSphere _ (physicalHarmonicExtension_contDiffAt (p j) ell)) first r u = 0) :
    ∀ q : PhysicalRealPolynomial, q.IsHomogeneous ell →
      homogeneousPairHarmonicMoment a k ha ha1 hk (physicalHarmonicExtension q ell)
        (continuous_harmonicSphere _ (physicalHarmonicExtension_contDiffAt q ell)) first r u = 0 := by
  let L := (physicalSphereMoment (homogeneousPairSphereFunction a k ha ha1 hk first r u)).comp
    physicalSpherePolynomial.toLinearMap
  have hp (j : J) : L (p j) = 0 := by
    have hj := hu j
    rw [homogeneousPairHarmonicMoment_eq_sphere] at hj
    exact hj
  intro q hq
  rw [homogeneousPairHarmonicMoment_eq_sphere]
  exact hspan L hp q hq

end DefocusingNLS

end OAI

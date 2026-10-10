import OAI.NumberTheory.PiExponent.Approximation.WeightedAffineParametrization
import OAI.NumberTheory.PiExponent.Geometry.CurveProperExtension

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveMonomialMap
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
open WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fromUnitCoordinate_projection
    {F E σ : Type u} [CommRing F] [CommRing E]
    (k : F →+* E) (y : σ → E) (z : σ) (hz : y z = 1) :
    fromUnitCoordinate (eval₂Hom k y) (by decide) (poly_X_mem z)
      (by simpa only [eval₂Hom_X', hz] using (isUnit_one : IsUnit (1 : E))) ≫
      polynomialProjectiveProjection F σ = Spec.map (CommRingCat.ofHom k) := by
  simp only [fromUnitCoordinate, polynomialProjectiveProjection, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X z)
    (by simpa only [eval₂Hom_X', hz] using (isUnit_one : IsUnit (1 : E)))
    (algebraMap (MvPolynomial σ F) (Localization.Away (X z)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

theorem affineChartMap_projection
    {F ι σ : Type u} [CommRing F]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := F) a z hz coordinate hcoordinate ≫ projection a =
      Spec.map (CommRingCat.ofHom (C : F →+* MvPolynomial ι F)) := by
  rw [projection, ← Category.assoc, affineChartMap_comp_projectiveMonomialMap]
  exact fromUnitCoordinate_projection C (fun s => monomial (a s) 1) z (by rw [hz]; exact MvPolynomial.C_1)

def genericMonomialMap
    {F E ι σ : Type u} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    Spec (CommRingCat.of E) ⟶ Proj (imageGrade (R := F) a) :=
  Spec.map (CommRingCat.ofHom (eval₂Hom (algebraMap F E) x)) ≫
    affineChartMap a z hz coordinate hcoordinate

theorem genericMonomialMap_over_base
    {F E ι σ : Type u} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    genericMonomialMap a z hz coordinate hcoordinate x ≫ projection a =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  rw [genericMonomialMap, Category.assoc, affineChartMap_projection,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  simp

end PiExponent.CurveMonomialMap

end

end OAI

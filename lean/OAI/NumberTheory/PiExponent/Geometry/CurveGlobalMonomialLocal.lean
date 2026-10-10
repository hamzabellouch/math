import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomial
import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveLocalCoefficients
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R A B σ : Type} [CommRing R] [CommRing A] [CommRing B]

theorem normalizedMap_natural (h : A →+* B) (k : R →+* A)
    (y : σ → A) (i : σ) (hi : y i = 1) :
    Spec.map (CommRingCat.ofHom h) ≫ normalizedMap k y i hi =
      normalizedMap (h.comp k) (fun j => h (y j)) i (by rw [hi, map_one]) := by
  unfold normalizedMap
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural h k y

theorem normalizedMap_scale (k : R →+* A) (a b : σ → A)
    (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Aˣ) (hscale : ∀ q, b q = (c : A) * a q) :
    normalizedMap k a i hi = normalizedMap k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := R) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A))
  have hg : IsUnit (g (MvPolynomial.X (R := R) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := R) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : A))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ R n →
      g p = (c : A) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : A) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold normalizedMap
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ R) (d := 1) f (by decide) (coordinates_X_mem (K := R) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ R) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := R) i) (coordinates_X_mem (K := R) j) hg hg')

end PiExponent.ProjectiveLocalCoefficients

namespace PiExponent.CurveGlobalMonomialLocal
open AlgebraicGeometry CategoryTheory MvPolynomial
open ProjectiveLatticePullback ProjectiveLocalCoefficients WeightedSectionOrder
open WeightedLocalLattice PiExponentSeshadri.Projective
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem latticeProjectiveMap_generic
    {F A E σ : Type} [CommRing F] [CommRing A] [IsDomain A]
    [Field E] [Algebra A E] [IsFractionRing A E] [Fintype σ]
    (k : F →+* A) (y : σ → E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y i})
    (z : σ) (hz : y z = 1) :
    Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ latticeProjectiveMap k y i hi hspan =
      normalizedMap ((algebraMap A E).comp k) y z hz := by
  rw [latticeProjectiveMap, normalizedMap_natural]
  apply normalizedMap_scale _ _ y i z _ hz (Units.mk0 (y i) hi)
  intro b
  change y b = y i * algebraMap A E (latticeCoordinates y i hi hspan b)
  rw [show algebraMap A E (latticeCoordinates y i hi hspan b) = y b / y i from
    coordinate_coefficient_image y Finset.univ i (Finset.mem_univ i) hi hspan b (Finset.mem_univ b)]
  field_simp

def monomialCoordinates {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (x : ι → E) (s : σ) : E :=
  eval₂Hom (algebraMap F E) x (monomial (a s) 1)

theorem monomialCoordinates_eq_prod
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E] [Fintype ι]
    (a : σ → ι →₀ ℕ) (x : ι → E) (s : σ) :
    monomialCoordinates (F := F) a x s = ∏ j, x j ^ (a s j) := by
  rw [monomialCoordinates, eval₂Hom_monomial, map_one, one_mul]
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

@[simp] theorem monomialCoordinates_zero
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0) :
    monomialCoordinates (F := F) a x z = 1 := by
  simp [monomialCoordinates, hz]

theorem genericMonomialMap_comp_projectiveMonomialMap
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x ≫
      WeightedCompactification.projectiveMonomialMap a =
      normalizedMap (algebraMap F E) (monomialCoordinates (F := F) a x) z
        (monomialCoordinates_zero a x z hz) := by
  have heval : (eval₂Hom (algebraMap F E) x).comp
        (WeightedCompactification.affineMonomialMap (R := F) a) =
      eval₂Hom (algebraMap F E) (monomialCoordinates (F := F) a x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [WeightedCompactification.affineMonomialMap]
    · intro b
      simp [WeightedCompactification.affineMonomialMap, monomialCoordinates]
  rw [CurveMonomialMap.genericMonomialMap, Category.assoc,
    WeightedCompactification.affineChartMap_comp_projectiveMonomialMap,
    fromUnitCoordinate_natural]
  unfold normalizedMap
  congr 1

theorem centerMorphism_eq_latticeProjectiveMap
    {F E σ : Type} [Field F] [Field E] [Algebra F E] [Fintype σ]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (g : CurveNormalizationModel.parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace F σ)
    (y : σ → E) (z : σ) (hz : y z = 1)
    (hg : CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g =
      normalizedMap (algebraMap F E) y z hz)
    (p : CurveValuationCenter.NormalizedPlace F E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p) y Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {y i}) :
    CurvePlaceCenter.centerMorphism f hf p ≫ g =
      latticeProjectiveMap (algebraMap F (PlaceValuationRing.ring p)) y i hi hspan := by
  apply CurvePlaceCenter.centerMorphism_comp_eq_of_generic f hf p
  rw [latticeProjectiveMap_generic _ y i hi hspan z hz, hg]
  rfl

theorem centerMorphism_globalMonomialMap
    {F E ι σ : Type} [Field F] [Field E] [Algebra F E] [Fintype σ]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ j, a (coordinate j) = Finsupp.single j 1)
    (x : ι → E)
    (g : CurveNormalizationModel.parameterCurve f hf ⟶
      Proj (WeightedCompactification.imageGrade (R := F) a))
    (hg : CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g =
      CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x)
    (p : CurveValuationCenter.NormalizedPlace F E) (i : σ)
    (hi : monomialCoordinates (F := F) a x i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p)
        (monomialCoordinates (F := F) a x) Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {monomialCoordinates (F := F) a x i}) :
    CurvePlaceCenter.centerMorphism f hf p ≫
        (g ≫ WeightedCompactification.projectiveMonomialMap a) =
      latticeProjectiveMap (algebraMap F (PlaceValuationRing.ring p))
        (monomialCoordinates (F := F) a x) i hi hspan := by
  apply centerMorphism_eq_latticeProjectiveMap f hf _ _ z
    (monomialCoordinates_zero a x z hz) _ p i hi hspan
  rw [← Category.assoc, hg]
  exact genericMonomialMap_comp_projectiveMonomialMap a z hz coordinate hcoordinate x

end PiExponent.CurveGlobalMonomialLocal

end

end OAI

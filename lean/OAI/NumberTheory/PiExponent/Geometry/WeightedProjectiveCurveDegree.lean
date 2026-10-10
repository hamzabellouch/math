import OAI.NumberTheory.PiExponent.Geometry.CurveContactSum
import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalCoordinateOrder
import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveLineBundle
import OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialFamilyLattice

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveValuationCenter
open PiExponent.CurveGlobalMonomialLocal PiExponent.WeightedPolynomialPole
open PiExponent.CurveGlobalCoordinateOrder

namespace PiExponent.WeightedProjectiveCurveDegree


variable {E ι σ : Type} [Field E] [Algebra ℂ E] [Fintype ι] [Fintype σ]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem ambient_pullback_degree
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (g : parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace ℂ σ)
    (hg : parameterCurveGenericPoint f hf ≫ g =
      ProjectiveLocalCoefficients.normalizedMap (algebraMap ℂ E)
        (monomialCoordinates (F := ℂ) a x) z (monomialCoordinates_zero a x z hz))
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  classical
  let y := monomialCoordinates (F := ℂ) a x
  have hyz : y z = 1 := monomialCoordinates_zero a x z hz
  have hyzn : y z ≠ 0 := hyz ▸ one_ne_zero
  let L := (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g
  let s := pullbackSection g (ProjectiveO1.coordinateSection z)
  have hs : s ≠ 0 := coordinateSection_ne_zero f hf g y z hyz hg z hyzn
  let D := CurvePlaceSectionDivisor.divisor f hf L s hs
  let P := CurveContactSum.weightedPoleDivisor hfinite x w
  have hcoeff : ∀ p, (D p : ℝ) = (R : ℝ) * (P p : ℝ) := by
    intro p
    obtain ⟨i, hi, horder, hspan⟩ := WeightedMonomialFamilyLattice.exists_generator
      p a x z hz w hw hR powers hpowers pure hpure hbudget
    have hd := coordinate_divisor_order f hf g y z hyz hg p i hi hspan z hyzn
    have hzero : coordinateOrder p.valuation (y z) = 0 := by
      rw [hyz]
      simp [coordinateOrder]
    rw [hzero, zero_sub] at hd
    have hq : (D p : ℚ) = R * coordinatePole p.valuation x w := by
      have hdq : (D p : ℚ) = -(coordinateOrder p.valuation (y i) : ℚ) := by
        exact_mod_cast hd
      rw [hdq, horder]
      ring
    exact_mod_cast hq
  let T := D.support ∪ P.support
  have hDT : D.support ⊆ T := Finset.subset_union_left
  have hPT : P.support ⊆ T := Finset.subset_union_right
  have hdeg := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf L s hs
  change ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
    eulerCharacteristic (parameterCurveStructureMap f hf) 1
      (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) = _
  rw [← hdeg]
  change ((D.sum (fun _ n => (n : ℤ)) : ℤ) : ℝ) = (R : ℝ) * P.sum (fun _ n => (n : ℝ))
  rw [D.sum_of_support_subset hDT (fun _ n => (n : ℤ)) (by simp),
    P.sum_of_support_subset hPT (fun _ n => (n : ℝ)) (by simp)]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => hcoeff p)

theorem weighted_pullback_degree
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ j, a (coordinate j) = Finsupp.single j 1)
    (g : parameterCurve f hf ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) a))
    (hg : parameterCurveGenericPoint f hf ≫ g =
      CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x)
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((WeightedCompactification.lineBundle (R := ℂ) a).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g (WeightedCompactification.projectiveMonomialMap a)).app
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
      ((WeightedCompactification.lineBundle (R := ℂ) a).pullback g).sheaf = _ at he
  rw [he]
  apply ambient_pullback_degree f hf a x z hz _ _ w hw hR powers hpowers pure hpure hbudget hfinite
  rw [← Category.assoc, hg]
  exact genericMonomialMap_comp_projectiveMonomialMap a z hz coordinate hcoordinate x

end PiExponent.WeightedProjectiveCurveDegree

end

end OAI

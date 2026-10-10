import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLatticePullback

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.WeightedSectionOrder PiExponent.LocalSectionOrder
open PiExponent.ProjectiveLatticePullback PiExponent.CurveLocalOrder

namespace PiExponent.ProjectiveLatticeOrder

variable {R A K σ : Type} [CommRing R] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Fintype σ]

theorem latticeCoordinates_order (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a})
    (b : σ) (hyb : y b ≠ 0) :
    ((IsDiscreteValuationRing.addVal A (latticeCoordinates y a hya hspan b)).toNat : ℤ) =
      WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y b) -
        WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y a) := by
  let c : A := latticeCoordinates y a hya hspan b
  have hc : c ≠ 0 := coordinate_coefficient_ne_zero y Finset.univ a
    (Finset.mem_univ a) hya hspan b (Finset.mem_univ b) hyb
  have hi := integerOrder_field_image_eq_length (K := K) hc
  have hu : Units.mk0 (algebraMap A K c)
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hc) =
      Units.mk0 (y b) hyb / Units.mk0 (y a) hya := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mk0]
    exact coordinate_coefficient_image y Finset.univ a (Finset.mem_univ a) hya hspan
      b (Finset.mem_univ b)
  rw [hu, WeightedCurveDegree.integerOrder_div, length_quotient_span_eq_addVal hc] at hi
  simpa only [WeightedPolynomialPole.coordinateOrder, dite_eq_right hyb, dite_eq_right hya] using hi.symm

theorem exists_frame_coordinate_orders
    (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    ∃ e : (Scheme.Modules.pullback (latticeProjectiveMap k y a hya hspan)).obj
      (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ b : σ, y b ≠ 0 →
      ((sectionOrder e (pullbackSection (latticeProjectiveMap k y a hya hspan)
        (ProjectiveO1.coordinateSection b))).toNat : ℤ) =
        WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y b) -
          WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y a) := by
  dsimp only [latticeProjectiveMap]
  obtain ⟨e, he⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients k
    (latticeCoordinates y a hya hspan) a (latticeCoordinates_self y a hya hspan)
  refine ⟨e, fun b hb => ?_⟩
  unfold sectionOrder
  rw [he]
  exact latticeCoordinates_order y a hya hspan b hb

end PiExponent.ProjectiveLatticeOrder

end

end OAI

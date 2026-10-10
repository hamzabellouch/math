import OAI.NumberTheory.PiExponent.Approximation.WeightedSectionOrder
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLocalCoefficients

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.WeightedSectionOrder PiExponent.LocalSectionOrder

namespace PiExponent.ProjectiveLatticePullback


variable {R A K σ : Type} [CommRing R] [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Fintype σ]

def latticeCoordinates (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) (b : σ) : A :=
  localCoefficient (A := A) (coordinateFrame y Finset.univ a (Finset.mem_univ a) hya hspan)
    (generatedSection y Finset.univ b (Finset.mem_univ b))

theorem latticeCoordinates_self (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    latticeCoordinates y a hya hspan a = 1 := by
  apply IsFractionRing.injective A K
  rw [map_one]
  exact (coordinate_coefficient_image y Finset.univ a (Finset.mem_univ a) hya hspan
    a (Finset.mem_univ a)).trans (div_self hya)

def latticeProjectiveMap (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    Spec (CommRingCat.of A) ⟶ ProjectiveO1.projectiveSpace R σ :=
  ProjectiveLocalCoefficients.normalizedMap k (latticeCoordinates y a hya hspan) a
    (latticeCoordinates_self y a hya hspan)

theorem exists_pullback_iso_preserving_sections
    (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    ∃ e : (Scheme.Modules.pullback (latticeProjectiveMap k y a hya hspan)).obj
        (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf ≅
      generatedSheaf (A := A) y Finset.univ,
      ∀ b : σ,
        pullbackSection (latticeProjectiveMap k y a hya hspan) (ProjectiveO1.coordinateSection b) ≫ e.hom =
          generatedSection (A := A) y Finset.univ b (Finset.mem_univ b) := by
  dsimp only [latticeProjectiveMap]
  let eL := coordinateFrame y Finset.univ a (Finset.mem_univ a) hya hspan
  obtain ⟨eP, heP⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients k
    (latticeCoordinates y a hya hspan) a (latticeCoordinates_self y a hya hspan)
  refine ⟨eP ≪≫ eL.symm, fun b => ?_⟩
  apply (cancel_mono eL.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply endValue_injective
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  exact heP b

theorem exists_pullback_frame_zeroEuler
    [IsDiscreteValuationRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    ∃ e : (Scheme.Modules.pullback (latticeProjectiveMap k y a hya hspan)).obj
        (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ b : σ, y b ≠ 0 → ∀ d : ℕ,
        sectionZeroEuler (A := A) e
          (pullbackSection (latticeProjectiveMap k y a hya hspan) (ProjectiveO1.coordinateSection b)) d =
          WeightedPolynomialPole.coordinateOrder (CurveLocalOrder.fractionAddValuation A K) (y b) -
            WeightedPolynomialPole.coordinateOrder (CurveLocalOrder.fractionAddValuation A K) (y a) := by
  dsimp only [latticeProjectiveMap]
  let eL := coordinateFrame y Finset.univ a (Finset.mem_univ a) hya hspan
  obtain ⟨eP, heP⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients k
    (latticeCoordinates y a hya hspan) a (latticeCoordinates_self y a hya hspan)
  refine ⟨eP, fun b hb d => ?_⟩
  have hc := heP b
  change localCoefficient (A := A) eP _ = localCoefficient (A := A) eL _ at hc
  have h := coordinate_zero_euler_eq_order_difference y Finset.univ a (Finset.mem_univ a)
    hya hspan b (Finset.mem_univ b) hb d
  unfold sectionZeroEuler LocalSectionOrder.zeroScheme at h ⊢
  rw [hc]
  exact h

end PiExponent.ProjectiveLatticePullback

end

end OAI

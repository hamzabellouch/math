import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoefficientNormalHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalHomologyDimension

namespace OAI

/-! # The rational dimension bound for an actual group extension

The finite total-complex comparison gives the sum of the kernel and quotient
bounds for every coefficient representation.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def coefficientNormalSecondPageIso {A : Rep.{0} ℤ G} (P : ProjectiveResolution A)
    (i j : ℕ) :
    (columnHomologyComplex
      (coefficientBarBicomplex (coefficientNormalQuotientComplex N P)) i).homology j ≅
      groupHomology ((coefficientNormalQuotientComplex N P).homology i) j := by
  classical
  exact (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
    (coefficientBarColumnHomologyIso (coefficientNormalQuotientComplex N P) i) ≪≫
    (groupHomologyIso ((coefficientNormalQuotientComplex N P).homology i) j
      (Rep.barResolution ℤ (G ⧸ N))).symm

theorem rational_homology_bound_of_extension {a b : ℕ}
    (hN : RationalHomologyDimensionLE N a) (hQ : RationalHomologyDimensionLE (G ⧸ N) b) :
    RationalHomologyDimensionLE G (a + b) := by
  classical
  intro A n hn
  let P := projectiveResolution A
  let C := coefficientNormalQuotientComplex N P
  let K := coefficientBarBicomplex C
  have hrow : ∀ p j, p + j = n →
      IsZero (rationalModuleFunctor.obj ((rowHomologyComplex K.flip j).homology p)) := by
    intro p j hpj
    have hz : IsZero (rationalModuleFunctor.obj (groupHomology (C.homology j) p)) := by
      by_cases hj : a < j
      · have hC : IsZero (rationalModuleFunctor.obj
            ((forget₂ (Rep ℤ (G ⧸ N)) (ModuleCat ℤ)).obj (C.homology j))) :=
          (hN (Rep.res N.subtype A) j hj).of_iso
            (rationalModuleFunctor.mapIso (coefficientNormalResolutionHomologyIso N P j))
        exact rational_groupHomology_isZero_of_coefficient (C.homology j) hC p
      · exact hQ (C.homology j) p (by omega)
    exact hz.of_iso (rationalModuleFunctor.mapIso (coefficientNormalSecondPageIso N P j p))
  have ht := rational_total_homology_isZero_of_secondPage K.flip n hrow
  let e := rationalModuleFunctor.mapIso
    ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ coefficientNormalTotalHomologyIso N P n)
  exact ht.of_iso e.symm

end PolycyclicRecognition

end

end OAI

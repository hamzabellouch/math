import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FreeRightCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BarCoefficientNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalDerivedHomologyFiniteness

namespace OAI

/-! # The other homology direction of the normal-extension bicomplex

Taking ambient-resolution homology gives the quotient group's actual bar
complex with coefficients in derived normal coinvariants. This identifies the
second homology page without treating it or its convergence as an input.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G]

def rightCoinvariantsNatTrans {B D : Rep.{0} ℤ G} (f : B ⟶ D) :
    rightCoinvariantsFunctor B ⟶ rightCoinvariantsFunctor D where
  app A := ((Rep.coinvariantsTensor ℤ G).obj A).map f
  naturality _ _ g := (((Rep.coinvariantsTensor ℤ G).map g).naturality f).symm

abbrev columnHomologyComplex (K : HomologicalComplex₂ (ModuleCat.{0} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (i : ℕ) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K.flip

variable (N : Subgroup G) [N.Normal]

def normalExtensionColumnHomologyBarIso
    (P : ProjectiveResolution (trivialIntegral G)) (i : ℕ) :
    columnHomologyComplex (normalExtensionBicomplex N P) i ≅
      (barCoefficientChainFunctor (G ⧸ N)).obj
        ((normalQuotientResolutionComplex N P).homology i) := by
  classical
  let C := normalQuotientResolutionComplex N P
  refine HomologicalComplex.Hom.isoOfComponents (fun j =>
    (C.sc i).mapHomologyIso (rightCoinvariantsFunctor ((Rep.barComplex ℤ (G ⧸ N)).X j))) ?_
  intro j k hjk
  let τ := rightCoinvariantsNatTrans ((Rep.barComplex ℤ (G ⧸ N)).d j k)
  symm
  change ShortComplex.homologyMap ((C.sc i).mapNatTrans τ) ≫
      ((C.sc i).mapHomologyIso (rightCoinvariantsFunctor ((Rep.barComplex ℤ (G ⧸ N)).X k))).hom =
    ((C.sc i).mapHomologyIso (rightCoinvariantsFunctor ((Rep.barComplex ℤ (G ⧸ N)).X j))).hom ≫
      τ.app (C.homology i)
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

def normalExtensionColumnSecondHomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (i j : ℕ) :
    (columnHomologyComplex (normalExtensionBicomplex N P) i).homology j ≅
      groupHomology ((normalQuotientResolutionComplex N P).homology i) j := by
  classical
  exact (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
      (normalExtensionColumnHomologyBarIso N P i) ≪≫
    (groupHomologyIso ((normalQuotientResolutionComplex N P).homology i) j
      (Rep.barResolution ℤ (G ⧸ N))).symm

/-- The canonical second page uses the derived quotient action on normal
subgroup homology, independent of the chosen ambient resolution. -/
def normalExtensionSecondPageIso
    (P : ProjectiveResolution (trivialIntegral G)) (i j : ℕ) :
    (columnHomologyComplex (normalExtensionBicomplex N P) i).homology j ≅
      groupHomology (normalDerivedHomology N i) j := by
  classical
  exact normalExtensionColumnSecondHomologyIso N P i j ≪≫
    (groupHomology.functor ℤ (G ⧸ N) j).mapIso
      (P.isoLeftDerivedObj (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) i).symm

end PolycyclicRecognition

end

end OAI

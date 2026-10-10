import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalAcyclicKernelHomology

namespace OAI

/-! # Computing homology from a resolution of the coefficient representation

The two actual bar directions identify derived coinvariants of an arbitrary
coefficient representation with its usual group homology. This is the
coefficient comparison needed when a locally finite kernel is removed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G]

def coefficientBarBicomplex (C : ChainComplex (Rep.{0} ℤ G) ℕ) : NatBicomplex :=
  (((Rep.coinvariantsTensor ℤ G).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj C).obj (Rep.barComplex ℤ G)

def coefficientBarRowOpcyclesIso (C : ChainComplex (Rep.{0} ℤ G) ℕ) :
    rowOpcyclesComplex (coefficientBarBicomplex C) ≅
      ((Rep.coinvariantsFunctor ℤ G).mapHomologicalComplex (ComplexShape.down ℕ)).obj C :=
  (Functor.mapHomologicalComplexCompIso (barCoefficientOpcyclesIso G)
    (ComplexShape.down ℕ)).app C

def coefficientBarColumnHomologyIso (C : ChainComplex (Rep.{0} ℤ G) ℕ) (i : ℕ) :
    columnHomologyComplex (coefficientBarBicomplex C) i ≅
      (barCoefficientChainFunctor G).obj (C.homology i) := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (fun j =>
    (C.sc i).mapHomologyIso (rightCoinvariantsFunctor ((Rep.barComplex ℤ G).X j))) ?_
  intro j k hjk
  let τ := rightCoinvariantsNatTrans ((Rep.barComplex ℤ G).d j k)
  symm
  change ShortComplex.homologyMap ((C.sc i).mapNatTrans τ) ≫
      ((C.sc i).mapHomologyIso (rightCoinvariantsFunctor ((Rep.barComplex ℤ G).X k))).hom =
    ((C.sc i).mapHomologyIso (rightCoinvariantsFunctor ((Rep.barComplex ℤ G).X j))).hom ≫
      τ.app (C.homology i)
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

def coefficientBarTotalRowHomologyIso (C : ChainComplex (Rep.{0} ℤ G) ℕ)
    (hC : ∀ i, Projective (C.X i)) (n : ℕ) :
    ((coefficientBarBicomplex C).total (ComplexShape.down ℕ)).homology n ≅
      (((Rep.coinvariantsFunctor ℤ G).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).homology n := by
  classical
  refine totalRowZeroHomologyIso (coefficientBarBicomplex C) ?_ n ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (coefficientBarRowOpcyclesIso C)
  intro i j
  let := hC i
  apply (((coefficientBarBicomplex C).X i).exactAt_iff_isZero_homology (j + 1)).mpr
  exact (projectiveCoefficient_groupHomology_succ_isZero (C.X i) j).of_iso
    (groupHomologyIso (C.X i) (j + 1) (Rep.barResolution ℤ G)).symm

def coefficientResolutionZeroHomologyIso {A : Rep.{0} ℤ G} (P : ProjectiveResolution A) :
    P.complex.homology 0 ≅ A :=
  isoOfQuasiIsoAt P.π 0 ≪≫ singleObjHomologySelfIso (ComplexShape.down ℕ) 0 A

def coefficientResolutionColumnOpcyclesIso {A : Rep.{0} ℤ G} (P : ProjectiveResolution A) :
    rowOpcyclesComplex (coefficientBarBicomplex P.complex).flip ≅
      (barCoefficientChainFunctor G).obj A :=
  (NatIso.mapHomologicalComplex chainZeroOpcyclesHomologyIso
    (ComplexShape.down ℕ)).app (coefficientBarBicomplex P.complex).flip ≪≫
      coefficientBarColumnHomologyIso P.complex 0 ≪≫
        (barCoefficientChainFunctor G).mapIso (coefficientResolutionZeroHomologyIso P)

def coefficientResolutionHomologyIso {A : Rep.{0} ℤ G} (P : ProjectiveResolution A) (n : ℕ) :
    (((Rep.coinvariantsFunctor ℤ G).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).homology n ≅ groupHomology A n := by
  classical
  let K := coefficientBarBicomplex P.complex
  have hex : ∀ j i, (K.flip.X j).ExactAt (i + 1) := by
    intro j i
    exact (P.complex_exactAt_succ i).map
      (rightCoinvariantsFunctor ((Rep.barComplex ℤ G).X j))
  exact (coefficientBarTotalRowHomologyIso P.complex (fun i => inferInstance) n).symm ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (K.totalFlipIso (ComplexShape.down ℕ)).symm ≪≫
    totalRowZeroHomologyIso K.flip hex n ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (coefficientResolutionColumnOpcyclesIso P) ≪≫
    (groupHomologyIso A n (Rep.barResolution ℤ G)).symm

end PolycyclicRecognition

end

end OAI

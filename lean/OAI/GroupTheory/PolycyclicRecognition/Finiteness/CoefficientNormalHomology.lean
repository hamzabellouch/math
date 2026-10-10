import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoefficientResolutionHomology

namespace OAI

/-! # Normal-extension comparison with arbitrary coefficients

Both bar directions retain the coefficient representation. A rationally
acyclic kernel then permits passage to its coinvariants in every degree.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def coefficientNormalQuotientComplex {A : Rep.{0} ℤ G} (P : ProjectiveResolution A) :
    ChainComplex (Rep.{0} ℤ (G ⧸ N)) ℕ :=
  ((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P.complex

def coefficientNormalResolutionHomologyIso {A : Rep.{0} ℤ G}
    (P : ProjectiveResolution A) (i : ℕ) :
    (forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)).obj
      ((coefficientNormalQuotientComplex N P).homology i) ≅
        groupHomology (Rep.res N.subtype A) i := by
  let C := coefficientNormalQuotientComplex N P
  let U := forget₂ (Rep.{0} ℤ (G ⧸ N)) (ModuleCat ℤ)
  let e := (NatIso.mapHomologicalComplex (quotientCoinvariantsUnderlyingIso N)
    (ComplexShape.down ℕ)).app P.complex
  exact ((C.sc i).mapHomologyIso U).symm ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso e ≪≫
    coefficientResolutionHomologyIso
      ((Rep.resFunctor.{0} N.subtype).mapProjectiveResolution P) i

def coefficientNormalTotalHomologyIso {A : Rep.{0} ℤ G}
    (P : ProjectiveResolution A) (i : ℕ) :
    ((coefficientBarBicomplex (coefficientNormalQuotientComplex N P)).total
      (ComplexShape.down ℕ)).homology i ≅ groupHomology A i :=
  coefficientBarTotalRowHomologyIso (coefficientNormalQuotientComplex N P)
    (fun j => Functor.projective_obj
      (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) (P.complex.X j)) i ≪≫
  (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso
    (iteratedCoinvariantsComplexIso N P.complex) ≪≫ coefficientResolutionHomologyIso P i

def coefficientNormalZeroHomologyIso {A : Rep.{0} ℤ G}
    (P : ProjectiveResolution A) :
    (coefficientNormalQuotientComplex N P).homology 0 ≅ A.quotientToCoinvariants N :=
  (P.isoLeftDerivedObj (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) 0).symm ≪≫
    (Rep.quotientToCoinvariantsFunctor.{0} ℤ N).leftDerivedZeroIsoSelf.app A

def coefficientNormalColumnOpcyclesIso {A : Rep.{0} ℤ G}
    (P : ProjectiveResolution A) :
    rowOpcyclesComplex (coefficientBarBicomplex (coefficientNormalQuotientComplex N P)).flip ≅
      (barCoefficientChainFunctor (G ⧸ N)).obj (A.quotientToCoinvariants N) :=
  (NatIso.mapHomologicalComplex chainZeroOpcyclesHomologyIso
    (ComplexShape.down ℕ)).app
      (coefficientBarBicomplex (coefficientNormalQuotientComplex N P)).flip ≪≫
  coefficientBarColumnHomologyIso (coefficientNormalQuotientComplex N P) 0 ≪≫
  (barCoefficientChainFunctor (G ⧸ N)).mapIso (coefficientNormalZeroHomologyIso N P)

theorem coefficientNormalColumn_rational_isZero {A : Rep.{0} ℤ G}
    (P : ProjectiveResolution A) (i j : ℕ)
    (hN : IsZero (rationalModuleFunctor.obj (groupHomology (Rep.res N.subtype A) i))) :
    IsZero (rationalModuleFunctor.obj
      (((coefficientBarBicomplex (coefficientNormalQuotientComplex N P)).flip.X j).homology i)) := by
  let C := coefficientNormalQuotientComplex N P
  let B := C.homology i
  have hB : IsZero (rationalModuleFunctor.obj
      ((forget₂ (Rep ℤ (G ⧸ N)) (ModuleCat ℤ)).obj B)) :=
    hN.of_iso (rationalModuleFunctor.mapIso (coefficientNormalResolutionHomologyIso N P i))
  let e := (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
    (coefficientBarColumnHomologyIso C i)
  exact (rational_coinvariantsTensor_isZero B ((Rep.barComplex ℤ (G ⧸ N)).X j) hB).of_iso
    (rationalModuleFunctor.mapIso e)

def rationalAcyclicKernelCoefficientHomologyIso (A : Rep.{0} ℤ G)
    (hN : ∀ i : ℕ, 0 < i →
      IsZero (rationalModuleFunctor.obj (groupHomology (Rep.res N.subtype A) i))) (n : ℕ) :
    rationalModuleFunctor.obj (groupHomology A n) ≅
      rationalModuleFunctor.obj (groupHomology (A.quotientToCoinvariants N) n) := by
  classical
  let P := projectiveResolution A
  let K := coefficientBarBicomplex (coefficientNormalQuotientComplex N P)
  have hz : ∀ j i, IsZero (rationalModuleFunctor.obj ((K.flip.X j).homology (i + 1))) :=
    fun j i => coefficientNormalColumn_rational_isZero N P (i + 1) j (hN _ (by omega))
  exact (rationalModuleFunctor.mapIso
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ coefficientNormalTotalHomologyIso N P n)).symm ≪≫
    rational_totalRowZeroHomologyIso K.flip hz n ≪≫
    rationalModuleFunctor.mapIso
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (coefficientNormalColumnOpcyclesIso N P)) ≪≫
    rationalModuleFunctor.mapIso
      (groupHomologyIso (A.quotientToCoinvariants N) n (Rep.barResolution ℤ (G ⧸ N))).symm

end PolycyclicRecognition

end

end OAI

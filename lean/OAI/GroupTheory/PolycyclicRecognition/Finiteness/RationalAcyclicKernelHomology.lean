import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalBicomplexComparison
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalCoinvariantsInflationIso
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalExtensionHomologyFiniteness

namespace OAI

/-! # Quotient homology after removing a rationally acyclic normal subgroup

The comparison is assembled from the actual two bar directions and the
degree-zero augmentation. No spectral-sequence collapse is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalExtensionColumnZeroOpcyclesIso
    (P : ProjectiveResolution (trivialIntegral G)) :
    rowOpcyclesComplex (normalExtensionBicomplex N P).flip ≅
      (barCoefficientChainFunctor (G ⧸ N)).obj (trivialIntegral (G ⧸ N)) :=
  (NatIso.mapHomologicalComplex chainZeroOpcyclesHomologyIso
    (ComplexShape.down ℕ)).app (normalExtensionBicomplex N P).flip ≪≫
  normalExtensionColumnHomologyBarIso N P 0 ≪≫
  (barCoefficientChainFunctor (G ⧸ N)).mapIso (normalQuotientResolutionZeroHomologyIso N P)

theorem normalExtensionColumn_rational_isZero
    (P : ProjectiveResolution (trivialIntegral G)) (i j : ℕ)
    (hN : IsZero (rationalModuleFunctor.obj (groupHomology (trivialIntegral N) i))) :
    IsZero (rationalModuleFunctor.obj
      (((normalExtensionBicomplex N P).flip.X j).homology i)) := by
  let A := (normalQuotientResolutionComplex N P).homology i
  have hA : IsZero (rationalModuleFunctor.obj
      ((forget₂ (Rep ℤ (G ⧸ N)) (ModuleCat ℤ)).obj A)) :=
    hN.of_iso (rationalModuleFunctor.mapIso (quotientResolutionHomologyIso N P i))
  let e := (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso
    (normalExtensionColumnHomologyBarIso N P i)
  exact (rational_coinvariantsTensor_isZero A ((Rep.barComplex ℤ (G ⧸ N)).X j) hA).of_iso
    (rationalModuleFunctor.mapIso e)

def rationalAcyclicKernelHomologyIso
    (hN : ∀ i : ℕ, 0 < i →
      IsZero (rationalModuleFunctor.obj (groupHomology (trivialIntegral N) i))) (n : ℕ) :
    rationalModuleFunctor.obj (groupHomology (trivialIntegral G) n) ≅
      rationalModuleFunctor.obj (groupHomology (trivialIntegral (G ⧸ N)) n) := by
  classical
  let P := Rep.barResolution ℤ G
  let K := normalExtensionBicomplex N P
  have hz : ∀ j i, IsZero (rationalModuleFunctor.obj ((K.flip.X j).homology (i + 1))) :=
    fun j i => normalExtensionColumn_rational_isZero N P (i + 1) j (hN _ (by omega))
  exact (rationalModuleFunctor.mapIso
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (K.totalFlipIso (ComplexShape.down ℕ)) ≪≫ normalExtensionTotalHomologyIso N P n)).symm ≪≫
    rational_totalRowZeroHomologyIso K.flip hz n ≪≫
    rationalModuleFunctor.mapIso
      ((homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (normalExtensionColumnZeroOpcyclesIso N P)) ≪≫
    rationalModuleFunctor.mapIso
      (groupHomologyIso (trivialIntegral (G ⧸ N)) n (Rep.barResolution ℤ (G ⧸ N))).symm

end PolycyclicRecognition

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Analysis.TrivialTensorChains
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

namespace OAI

/-! # Rational tensoring commutes with the homology used here -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory MonoidalCategory

def rationalChainHomologyIso (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (((tensorLeft (ModuleCat.of ℤ ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n ≅
      (tensorLeft (ModuleCat.of ℤ ℚ)).obj (C.homology n) :=
  (C.sc n).mapHomologyIso (tensorLeft (ModuleCat.of ℤ ℚ))

theorem rationalChainHomologyIso_naturality {C D : ChainComplex (ModuleCat ℤ) ℕ}
    (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((tensorLeft (ModuleCat.of ℤ ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
        (rationalChainHomologyIso D n).hom =
      (rationalChainHomologyIso C n).hom ≫
        (tensorLeft (ModuleCat.of ℤ ℚ)).map (HomologicalComplex.homologyMap f n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map f)
    (tensorLeft (ModuleCat.of ℤ ℚ))

def rationalTensorHomologyIso {G : Type} [Group G] [DecidableEq G]
    (A : Rep ℤ G) (n : ℕ) :
    groupHomology (trivialTensorCoefficient (ModuleCat.of ℤ ℚ) A) n ≅
      (tensorLeft (ModuleCat.of ℤ ℚ)).obj (groupHomology A n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (trivialTensorChainsIso (ModuleCat.of ℤ ℚ) A).symm ≪≫
    rationalChainHomologyIso (groupHomology.inhomogeneousChains A) n

end PolycyclicRecognition

end

end OAI

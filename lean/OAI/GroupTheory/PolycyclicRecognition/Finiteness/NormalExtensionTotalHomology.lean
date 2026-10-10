import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexRowHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BarCoefficientNaturality

namespace OAI

/-! # The normal-extension total complex computes ambient group homology

This comparison is proved from finite antidiagonal elimination, the exact
bar resolution, and actual iterated coinvariants. No convergence or extension
existence is introduced as a hypothesis.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalExtensionRowOpcyclesIso (P : ProjectiveResolution (trivialIntegral G)) :
    rowOpcyclesComplex (normalExtensionBicomplex N P) ≅
      ((Rep.coinvariantsFunctor ℤ (G ⧸ N)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (normalQuotientResolutionComplex N P) :=
  (Functor.mapHomologicalComplexCompIso (barCoefficientOpcyclesIso (G ⧸ N))
    (ComplexShape.down ℕ)).app (normalQuotientResolutionComplex N P)

def normalExtensionTotalHomologyIso (P : ProjectiveResolution (trivialIntegral G)) (n : ℕ) :
    ((normalExtensionBicomplex N P).total (ComplexShape.down ℕ)).homology n ≅
      groupHomology (trivialIntegral G) n :=
  normalExtensionTotalRowZeroHomologyIso N P n ≪≫
    (homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
      (normalExtensionRowOpcyclesIso N P) ≪≫
    iteratedResolutionHomologyIso N P n

end PolycyclicRecognition

end

end OAI

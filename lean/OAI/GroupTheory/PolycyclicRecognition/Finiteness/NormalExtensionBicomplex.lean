import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalCoinvariantsProjective
import Mathlib.Algebra.Homology.Bifunctor

namespace OAI

/-! # The normal-extension bar bicomplex

One direction is the ambient resolution after normal coinvariants; the other
is the quotient group's actual bar resolution. Its row homology is identified
with actual quotient-group homology, and row degree zero with ordinary ambient
coinvariants. No spectral-sequence convergence is assumed here.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalQuotientResolutionComplex (P : ProjectiveResolution (trivialIntegral G)) :
    ChainComplex (Rep.{0} ℤ (G ⧸ N)) ℕ :=
  ((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj P.complex

def normalExtensionBicomplex (P : ProjectiveResolution (trivialIntegral G)) :
    HomologicalComplex₂ (ModuleCat ℤ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((Rep.coinvariantsTensor ℤ (G ⧸ N)).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
        (normalQuotientResolutionComplex N P)).obj (Rep.barComplex ℤ (G ⧸ N))

instance normalQuotientResolutionComplex_projective
    (P : ProjectiveResolution (trivialIntegral G)) (i : ℕ) :
    Projective ((normalQuotientResolutionComplex N P).X i) :=
  normalCoinvariantsResolutionTerm_projective N P i

def normalExtensionRowHomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (i j : ℕ) :
    ((normalExtensionBicomplex N P).X i).homology j ≅
      groupHomology ((normalQuotientResolutionComplex N P).X i) j := by
  classical
  exact (groupHomologyIso ((normalQuotientResolutionComplex N P).X i) j
    (Rep.barResolution ℤ (G ⧸ N))).symm

def normalExtensionRowZeroIso
    (P : ProjectiveResolution (trivialIntegral G)) (i : ℕ) :
    ((normalExtensionBicomplex N P).X i).homology 0 ≅
      (Rep.coinvariantsFunctor ℤ G).obj (P.complex.X i) :=
  normalExtensionRowHomologyIso N P i 0 ≪≫
    groupHomology.H0Iso ((normalQuotientResolutionComplex N P).X i) ≪≫
      (iteratedCoinvariantsEquiv N (P.complex.X i)).toModuleIso

end PolycyclicRecognition

end

end OAI

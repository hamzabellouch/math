import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientResolutionHomology

namespace OAI

/-! # FP finiteness of the canonical quotient action on subgroup homology

The action is defined by deriving normal-subgroup coinvariants. Its underlying
integral module is the usual subgroup homology. Its finite generation follows
from the actual finite terms in an ambient projective resolution.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def normalDerivedHomology (i : ℕ) : Rep ℤ (G ⧸ N) :=
  ((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).leftDerived i).obj (trivialIntegral G)

def normalDerivedHomologyIso (i : ℕ) :
    (forget₂ (Rep ℤ (G ⧸ N)) (ModuleCat ℤ)).obj (normalDerivedHomology N i) ≅
      groupHomology (Rep.trivial ℤ N ℤ) i :=
  (forget₂ (Rep ℤ (G ⧸ N)) (ModuleCat ℤ)).mapIso
      ((Rep.barResolution ℤ G).isoLeftDerivedObj
        (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) i) ≪≫
    quotientResolutionHomologyIso N (Rep.barResolution ℤ G) i

theorem typeFP_normalDerivedHomology_finite
    [IsMulCommutative (G ⧸ N)] [Group.FG (G ⧸ N)] (i : ℕ) (h : TypeFP G i) :
    IntegralRepresentationFinite (G ⧸ N) (normalDerivedHomology N i) := by
  obtain ⟨P, hP⟩ := typeFP_quotientCoinvariants_homology N i h
  exact (hP i le_rfl).of_iso
    (P.isoLeftDerivedObj (Rep.quotientToCoinvariantsFunctor.{0} ℤ N) i).symm

theorem typeFPInfinity_normalDerivedHomology_finite
    [Group.FG G] [IsMulCommutative (G ⧸ N)] (h : TypeFPInfinity G) (i : ℕ) :
    IntegralRepresentationFinite (G ⧸ N) (normalDerivedHomology N i) :=
  typeFP_normalDerivedHomology_finite N i (h i)

end PolycyclicRecognition

end

end OAI

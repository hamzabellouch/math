import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularFreeEvaluation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularPairingNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteProjectivePresentations

namespace OAI

/-! # Regular-dual evaluation for finite projective modules

Naturality passes the finite free evaluation isomorphism to its projective
retracts. This is the termwise comparison for top-degree duality.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem regularCoinvariantEvaluation_bijective (P A : Rep ℤ G)
    [Projective P] (hP : IntegralRepresentationFinite G P) :
    Function.Bijective (regularCoinvariantEvaluation P A) := by
  classical
  obtain ⟨ι, hι, q, hq⟩ := finiteIntegralFreeCover_exists P hP
  let := hι
  let := hq
  let s := Projective.factorThru (𝟙 P) q
  have hs : s ≫ q = 𝟙 P := Projective.factorThru_comp (𝟙 P) q
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  have hfree : Function.Bijective (regularCoinvariantEvaluation (Rep.free ℤ G ι) A) := by
    rw [← regularFreeEvaluationEquiv_eq]
    exact (regularFreeEvaluationEquiv ι A).bijective
  constructor
  · intro x y hxy
    have he : regularCoinvariantEvaluation (Rep.free ℤ G ι) A (F.map s x) =
        regularCoinvariantEvaluation (Rep.free ℤ G ι) A (F.map s y) := by
      rw [regularCoinvariantEvaluation_naturality, regularCoinvariantEvaluation_naturality,
        hxy]
    have he' := congrArg (fun z => F.map q z) (hfree.1 he)
    simpa only [← ModuleCat.comp_apply, ← F.map_comp, hs, F.map_id,
      ModuleCat.id_apply] using he'
  · intro y
    obtain ⟨x, hx⟩ := hfree.2 (regularDualMap s ≫ y)
    refine ⟨F.map q x, ?_⟩
    rw [regularCoinvariantEvaluation_naturality, hx, ← Category.assoc,
      ← regularDualMap_comp, hs, regularDualMap_id, Category.id_comp]

def regularProjectiveEvaluationEquiv (P A : Rep ℤ G) [Projective P]
    (hP : IntegralRepresentationFinite G P) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj P ≃ₗ[ℤ] (regularDual P ⟶ A) :=
  LinearEquiv.ofBijective (regularCoinvariantEvaluation P A)
    (regularCoinvariantEvaluation_bijective P A hP)

end PolycyclicRecognition

end

end OAI

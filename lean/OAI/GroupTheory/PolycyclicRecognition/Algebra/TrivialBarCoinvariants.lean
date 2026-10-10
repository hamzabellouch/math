import OAI.GroupTheory.PolycyclicRecognition.Finiteness.QuotientResolutionHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AutomorphismCoinvariants
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalBarConjugation

namespace OAI

/-! # Integral bar chains as coinvariants of the free bar resolution -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G)

def trivialBarCoinvariantsIso [DecidableEq N] :
    groupHomology.inhomogeneousChains (Rep.trivial ℤ N ℤ) ≅
      ((Rep.coinvariantsFunctor ℤ N).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.barComplex ℤ N) :=
  groupHomology.inhomogeneousChainsIso (Rep.trivial ℤ N ℤ) ≪≫
    ((NatIso.mapHomologicalComplex (trivialCoinvariantsTensorIso N)
      (ComplexShape.down ℕ)).app (Rep.barComplex ℤ N)).symm

@[simp] theorem trivialBarCoinvariantsIso_single [DecidableEq N]
    (i : ℕ) (x : Fin i → N) (r : ℤ) :
    ((trivialBarCoinvariantsIso N).hom.f i) (Finsupp.single x r) =
      Representation.Coinvariants.mk (Representation.free ℤ N (Fin i → N))
        (Finsupp.single x (MonoidAlgebra.single 1 r)) := by
  change ((Rep.coinvariantsFunctor ℤ N).map
      (λ_ (Rep.free ℤ N (Fin i → N))).hom)
    (Rep.finsuppToCoinvariantsTensorFree (Rep.trivial ℤ N ℤ) (Fin i → N)
      (Finsupp.single x r)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change Representation.Coinvariants.mk _
    ((λ_ (Rep.free ℤ N (Fin i → N))).hom.hom
      (r ⊗ₜ[ℤ] (Finsupp.single x (MonoidAlgebra.single 1 1)))) = _
  congr 1
  change r • Finsupp.single x (MonoidAlgebra.single 1 1) = _
  simp

def normalSubgroupBarChains [DecidableEq N] :
    groupHomology.inhomogeneousChains (Rep.trivial ℤ N ℤ) ⟶
      ((Rep.resFunctor.{0} N.subtype ⋙ Rep.coinvariantsFunctor ℤ N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Rep.barComplex ℤ G) :=
  (trivialBarCoinvariantsIso N).hom ≫
    ((Rep.coinvariantsFunctor ℤ N).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (subgroupBarResolutionMap N)

@[simp] theorem normalSubgroupBarChains_single [DecidableEq N]
    (i : ℕ) (x : Fin i → N) (r : ℤ) :
    (normalSubgroupBarChains N).f i (Finsupp.single x r) =
      Representation.Coinvariants.mk
        ((Representation.free ℤ G (Fin i → G)).comp N.subtype)
        (Finsupp.single (N.subtype ∘ x) (MonoidAlgebra.single 1 r)) := by
  change ((Rep.coinvariantsFunctor ℤ N).map (subgroupFreeInclusion N i))
    (((trivialBarCoinvariantsIso N).hom.f i) (Finsupp.single x r)) = _
  rw [trivialBarCoinvariantsIso_single]
  change Representation.Coinvariants.mk _
    ((subgroupFreeInclusion N i).hom (Finsupp.single x (MonoidAlgebra.single 1 r))) = _
  rw [subgroupFreeInclusion_single]
  rfl

end PolycyclicRecognition

end

end OAI

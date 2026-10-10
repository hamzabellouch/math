import OAI.GroupTheory.PolycyclicRecognition.Algebra.IteratedCoinvariants
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyModuleFiniteness

namespace OAI

/-! # Iterated coinvariants of an ambient resolution

The natural degree-zero comparison extends to complexes and identifies their
homology with actual group homology. This retains the ambient resolution for
the subsequent filtration argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def iteratedCoinvariantsFunctorIso :
    Rep.quotientToCoinvariantsFunctor.{0} ℤ N ⋙ Rep.coinvariantsFunctor ℤ (G ⧸ N) ≅
      Rep.coinvariantsFunctor ℤ G :=
  NatIso.ofComponents (fun A => (iteratedCoinvariantsEquiv N A).toModuleIso) (by
    intro A B f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Representation.Coinvariants.induction_on with
    | h x =>
      induction x using Representation.Coinvariants.induction_on with
      | h x => rfl)

def iteratedCoinvariantsComplexIso (K : ChainComplex (Rep.{0} ℤ G) ℕ) :
    ((Rep.coinvariantsFunctor ℤ (G ⧸ N)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K) ≅
      ((Rep.coinvariantsFunctor ℤ G).mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
  (Functor.mapHomologicalComplexCompIso (iteratedCoinvariantsFunctorIso N)
    (ComplexShape.down ℕ)).app K

def groupTrivialCoinvariantsTensorIso :
    Rep.coinvariantsFunctor.{0} ℤ G ≅
      (Rep.coinvariantsTensor ℤ G).obj (trivialIntegral G) :=
  NatIso.ofComponents
    (fun A => (Rep.coinvariantsFunctor ℤ G).mapIso (λ_ A).symm) (by
      intro A B f
      change (Rep.coinvariantsFunctor ℤ G).map f ≫
          (Rep.coinvariantsFunctor ℤ G).map (λ_ B).inv =
        (Rep.coinvariantsFunctor ℤ G).map (λ_ A).inv ≫
          (Rep.coinvariantsFunctor ℤ G).map ((𝟙 (𝟙_ (Rep ℤ G))) ⊗ₘ f)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1)

def iteratedResolutionHomologyIso
    (P : ProjectiveResolution (trivialIntegral G)) (i : ℕ) :
    (((Rep.coinvariantsFunctor ℤ (G ⧸ N)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((Rep.quotientToCoinvariantsFunctor.{0} ℤ N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex)).homology i ≅
      groupHomology (trivialIntegral G) i := by
  classical
  let e := iteratedCoinvariantsComplexIso N P.complex ≪≫
    (NatIso.mapHomologicalComplex (groupTrivialCoinvariantsTensorIso (G := G))
      (ComplexShape.down ℕ)).app P.complex
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) i).mapIso e ≪≫
    (groupHomologyIso (trivialIntegral G) i P).symm

end PolycyclicRecognition

end

end OAI

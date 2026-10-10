import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegerExtensionDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InducedResolutionHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CofiberChainHomology

namespace OAI

/-! # Top homology of an infinite cyclic extension

Tensoring the explicit mapping-cone resolution reduces the top degree to the
kernel of the induced translation difference on subgroup homology.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)
  [IsCyclic (G ⧸ q.ker)] [Infinite (G ⧸ q.ker)]
  (P : ProjectiveResolution (trivialIntegral q.ker)) (A : Rep ℤ G)

local instance : CommGroup (G ⧸ q.ker) := IsCyclic.commGroup

def integerExtensionTensorMap :=
  (((Rep.coinvariantsTensor ℤ G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (integerExtensionMap q t P)

def integerExtensionHomologyKernelIso (i : ℕ)
    (hN : IsZero (groupHomology (Rep.res q.ker.subtype A) (i + 1))) :
    groupHomology A (i + 1) ≅
      kernel (HomologicalComplex.homologyMap (integerExtensionTensorMap q t P A) i) := by
  classical
  let F := (Rep.coinvariantsTensor ℤ G).obj A
  have hz : IsZero
      (((quotientInducedResolution q.ker P).complex.coinvariantsTensorObj A).homology (i + 1)) :=
    IsZero.of_iso hN (inducedResolutionHomologyIso q.ker A P (i + 1))
  exact groupHomologyIso A (i + 1) (integerExtensionResolution q t ht P) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (i + 1)).mapIso
      (homotopyCofiber.mapHomologicalComplexObjIso (integerExtensionMap q t P) F) ≪≫
    cofiberChainHomologyKernelIso (integerExtensionTensorMap q t P A) i hz

end PolycyclicRecognition

end

end OAI

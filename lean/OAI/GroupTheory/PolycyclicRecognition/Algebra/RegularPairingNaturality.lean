import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularDualPairing

namespace OAI

/-! # Naturality of the regular-dual evaluation pairing -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
variable {G : Type} [Group G]

@[simp] theorem regularDualMap_id (P : Rep ℤ G) :
    regularDualMap (𝟙 P) = 𝟙 (regularDual P) := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro f
  exact Category.id_comp f

theorem regularDualMap_comp {P Q R : Rep ℤ G} (f : P ⟶ Q) (g : Q ⟶ R) :
    regularDualMap (f ≫ g) = regularDualMap g ≫ regularDualMap f := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro h
  exact Category.assoc f g h

theorem regularCoinvariantEvaluation_naturality {P Q : Rep ℤ G} (f : P ⟶ Q)
    (A : Rep ℤ G) (x : ((Rep.coinvariantsTensor ℤ G).obj A).obj P) :
    regularCoinvariantEvaluation Q A (((Rep.coinvariantsTensor ℤ G).obj A).map f x) =
      regularDualMap f ≫ regularCoinvariantEvaluation P A x := by
  refine Representation.Coinvariants.induction_on x ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a p =>
    apply Rep.hom_ext
    apply DFunLike.ext
    intro q
    rfl
  | add t u ht hu =>
    simp only [map_add, Preadditive.comp_add, ht, hu]

end PolycyclicRecognition

end

end OAI

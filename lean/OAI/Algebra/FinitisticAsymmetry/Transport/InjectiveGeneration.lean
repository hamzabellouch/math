import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Transport.DerivedEquivalence

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section InjectiveGenerationTransport
universe v
variable {R S : Type v} [Ring R] [Ring S]
open CategoryTheory.Limits

lemma injectivesGenerate_of_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) (hR : InjectivesGenerate R) :
    InjectivesGenerate S := by
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  let := HasDerivedCategory.standard (ModuleCat.{v} S)
  let : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  let F := e.functor.mapDerivedCategory
  let : F.IsEquivalence := mapDerivedCategory_isEquivalence e
  intro P hP hT hCol hI X
  let := hP
  let := hT
  let (index : Type v) := hCol index
  have h : ∀ Y, (P.inverseImage F) Y := by
    apply hR (P.inverseImage F) inferInstance inferInstance (fun I => inferInstance)
    intro M hM
    let := hM
    exact P.prop_of_iso ((e.functor.mapDerivedCategorySingleFunctor 0).app M).symm
      (hI (e.functor.obj M) inferInstance)
  exact P.prop_of_iso (F.asEquivalence.counitIso.app X) (h (F.asEquivalence.inverse.obj X))

lemma injectivesGenerate_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    InjectivesGenerate R ↔ InjectivesGenerate S :=
  ⟨injectivesGenerate_of_equivalence e, injectivesGenerate_of_equivalence e.symm⟩

end InjectiveGenerationTransport

end LittleFinitistic
end
end
end

end OAI

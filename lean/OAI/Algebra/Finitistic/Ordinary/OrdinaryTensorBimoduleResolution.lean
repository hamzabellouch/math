import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedBimodule
import OAI.Algebra.Finitistic.Ordinary.OrdinaryIntegerResolution
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFunctorExtension

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

abbrev bimoduleTerm (n : ℕ) := RetainedBimodule k B (B ⊗[k] ChainAlgebra k l) (term k B l n)

def bimoduleDifferential (n : ℕ) :=
  RetainedBimodule.map (k := k) (S := B) (A := B ⊗[k] ChainAlgebra k l) (differential k B l n) (differential_left k B l n)

theorem bimoduleDifferential_square (n : ℕ) :
    (bimoduleDifferential k B l (n+1)).comp (bimoduleDifferential k B l n) = 0 := by
  apply LinearMap.ext
  intro x
  exact congrArg (fun f => f x) (differential_square k B l n)

/-- The actual finite resolution retains the left B-action as a genuine tensor-algebra complex. -/
def bimoduleComplex : CochainComplex (ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of _ (bimoduleTerm k B l n))
    (fun n => ModuleCat.ofHom (bimoduleDifferential k B l n))
    (fun n => ModuleCat.hom_ext (bimoduleDifferential_square k B l n))

/-- The genuine bimodule resolution in exactly the source interval [-l,0]. -/
def integerBimoduleComplex : CochainComplex (ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)) ℤ :=
  (bimoduleComplex k B l).extend (degreeEmbedding l)

abbrev forgetBimodule : ModuleCat.{u} (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) ⥤
    ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ :=
  ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)).toRingHom

def forgetBimoduleTerm (n : ℕ) :
    (forgetBimodule k B l).obj (ModuleCat.of _ (bimoduleTerm k B l n)) ≅ termObject k B l n := by
  let e : (forgetBimodule k B l).obj (ModuleCat.of _ (bimoduleTerm k B l n)) ≃ₗ[(B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ]
      term k B l n :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        change TensorIdeal.coefficient (1:B) * (x.val * r.unop) = x.val * r.unop
        rw [map_one,one_mul] }
  exact e.toModuleIso

/-- Forgetting the retained left action recovers the verified ordinary finite resolution. -/
def forgetBimoduleComplex :
    ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).obj (bimoduleComplex k B l) ≅ complex k B l :=
  HomologicalComplex.Hom.isoOfComponents (forgetBimoduleTerm k B l) (by
    intro n m h
    change n+1=m at h
    subst m
    change (forgetBimoduleTerm k B l n).hom ≫ (complex k B l).d n (n+1) =
      (forgetBimodule k B l).map ((bimoduleComplex k B l).d n (n+1)) ≫ (forgetBimoduleTerm k B l (n+1)).hom
    have h₁ : (complex k B l).d n (n+1) = ModuleCat.ofHom (differential k B l n) :=
      CochainComplex.of_d (termObject k B l) (fun n => ModuleCat.ofHom (differential k B l n)) n
    have h₂ : (bimoduleComplex k B l).d n (n+1) = ModuleCat.ofHom (bimoduleDifferential k B l n) :=
      CochainComplex.of_d (fun n => ModuleCat.of (B ⊗[k] (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) (bimoduleTerm k B l n))
        (fun n => ModuleCat.ofHom (bimoduleDifferential k B l n)) n
    rw [h₁,h₂]
    rfl)

/-- Every integer term and differential agrees after forgetting the left action. -/
def forgetIntegerBimoduleComplex :
    ((forgetBimodule k B l).mapHomologicalComplex (.up ℤ)).obj (integerBimoduleComplex k B l) ≅
      integerComplex k B l :=
  FunctorExtension.iso (forgetBimodule k B l) (bimoduleComplex k B l) (degreeEmbedding l) ≪≫
    ((degreeEmbedding l).extendFunctor _).mapIso (forgetBimoduleComplex k B l)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI

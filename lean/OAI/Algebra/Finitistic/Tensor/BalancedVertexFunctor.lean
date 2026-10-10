import OAI.Algebra.Finitistic.Tensor.BalancedVertexImage

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.BalancedVertexFunctor
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (e : B) (he : e*e=e)
variable (N : Type u) [AddCommGroup N] [Module k N] [Module B N]

abbrev Space (M : ModuleCat.{u} (Enveloping k B)) :=
  IdempotentTensor.leftSpace (k := k) e (BimoduleBalancedTensor.Tensor k B M N)

def spaceMap {M M' : ModuleCat.{u} (Enveloping k B)} (f : M ⟶ M') :
    Space k B e N M →ₗ[k] Space k B e N M' :=
  (((BimoduleBalancedTensor.map k B N f).restrictScalars k).comp
    (Space k B e N M).subtype).codRestrict _ (by
      intro x
      change e • (BimoduleBalancedTensor.map k B N f x.val) =
        BimoduleBalancedTensor.map k B N f x.val
      rw [← (BimoduleBalancedTensor.map k B N f).map_smul,x.property])

/-- The actual left vertex of the balanced tensor, with its original induced maps. -/
def functor : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (Space k B e N M)
  map f := ModuleCat.ofHom (spaceMap k B e N f)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : (BimoduleBalancedTensor.functor k B N).obj M ⟶
        (BimoduleBalancedTensor.functor k B N).obj M => f.hom x.val)
      ((BimoduleBalancedTensor.functor k B N).map_id M)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => ModuleCat.Hom.hom f x.val)
      ((BimoduleBalancedTensor.functor k B N).map_comp f g)

instance additive : (functor k B e N).Additive where
  map_add := by
    intros M M' f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun a : (BimoduleBalancedTensor.functor k B N).obj M ⟶
      (BimoduleBalancedTensor.functor k B N).obj M' => a.hom x.val)
      ((BimoduleBalancedTensor.functor k B N).map_add (f := f) (g := g))

/-- Vertex extraction commutes naturally with the original balanced tensor functor. -/
def comparison : BimoduleVertex.functor k B e ⋙ BalancedTensor.tensorFunctor k B N ≅
    functor k B e N :=
  NatIso.ofComponents (fun M => (BalancedVertexImage.equiv k B M e he N).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hn : (BimoduleVertex.functor k B e).map f ≫ BalancedVertexImage.inclusion k B M' e =
        BalancedVertexImage.inclusion k B M e ≫ (forgetRight k B).map f := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      rfl
    have hF := congrArg (fun a => (BalancedTensor.tensorFunctor k B N).map a) hn
    simp only [Functor.map_comp] at hF
    exact congrArg (fun a => ModuleCat.Hom.hom a x) hF)

/-- The natural comparison gives an actual chain isomorphism on every bimodule complex. -/
def complexIso (P : BiComplex k B) :
    ((BimoduleVertex.functor k B e ⋙ BalancedTensor.tensorFunctor k B N).mapHomologicalComplex (.up ℤ)).obj P ≅
      ((functor k B e N).mapHomologicalComplex (.up ℤ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (comparison k B e he N).app (P.X n))
    (fun n m _ => ((comparison k B e he N).hom.naturality (P.d n m)).symm)
end LittleFinitistic.BalancedVertexFunctor

end

end OAI

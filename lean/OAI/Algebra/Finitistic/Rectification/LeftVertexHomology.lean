import OAI.Algebra.Finitistic.Rectification.VertexHomology
import OAI.Algebra.Finitistic.Rectification.VertexDecomposition

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.LeftVertexHomology
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

lemma scalar_commute (e : B) (c : k) : e * algebraMap k B c = algebraMap k B c * e :=
  (Algebra.commutes c e).symm

/-- The actual left vertex functor from B-modules to k-vector spaces. -/
abbrev vertex (e : B) : ModuleCat.{u} B ⥤ ModuleCat.{u} k :=
  VertexFunctor.functor (algebraMap k B) e (scalar_commute k B e)

/-- Arrow action is a natural transformation between the actual vertex functors. -/
def arrow (ei ej a : B) (ha : ej*a=a) : vertex k B ei ⟶ vertex k B ej where
  app M := ModuleCat.ofHom {
    toFun := fun x => ⟨a • (x.val : M), by
      rw [VertexFunctor.mem_fixed]
      rw [← mul_smul, ha]⟩
    map_add' := fun x y => Subtype.ext (smul_add _ _ _)
    map_smul' := fun c x => by
      apply Subtype.ext
      change a • (algebraMap k B c • (x.val : M)) =
        algebraMap k B c • (a • (x.val : M))
      rw [← mul_smul, ← mul_smul, scalar_commute] }
  naturality M M' f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (f.hom.map_smul a x.val).symm

instance scalarTower (M : ModuleCat.{u} B) :
    IsScalarTower k B ((ModuleCat.restrictScalars (algebraMap k B)).obj M) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Identify the vertex functor with the actual fixed subspace of scalar restriction. -/
def spaceEquiv (e : B) (M : ModuleCat.{u} B) :
    (vertex k B e).obj M ≃ₗ[k]
      IdempotentTensor.leftSpace (k := k) e ((ModuleCat.restrictScalars (algebraMap k B)).obj M) where
  toFun x := ⟨x.val, (VertexFunctor.mem_fixed _ _ _ M x.val).1 x.property⟩
  invFun x := ⟨x.val, (VertexFunctor.mem_fixed _ _ _ M x.val).2 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual vertex homology, identified with the actual subspace of module homology. -/
def homologyEquiv (e : B) (he : e*e=e)
    (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    (((vertex k B e).mapHomologicalComplex (.up ℤ)).obj X).homology n ≃ₗ[k]
      IdempotentTensor.leftSpace (k := k) e
        ((ModuleCat.restrictScalars (algebraMap k B)).obj (X.homology n)) :=
  (VertexHomology.iso (algebraMap k B) e he (scalar_commute k B e) X n).toLinearEquiv.trans
    (spaceEquiv k B e (X.homology n))

/-- Cohomology comparison retains the original arrow action, not only dimensions. -/
theorem arrow_homology (ei ej a : B) (hi : ei*ei=ei) (hj : ej*ej=ej) (ha : ej*a=a)
    (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    homologyMap ((NatTrans.mapHomologicalComplex (arrow k B ei ej a ha) (.up ℤ)).app X) n ≫
      (VertexHomology.iso (algebraMap k B) ej hj (scalar_commute k B ej) X n).hom =
    (VertexHomology.iso (algebraMap k B) ei hi (scalar_commute k B ei) X n).hom ≫
      (arrow k B ei ej a ha).app (X.homology n) :=
  VertexHomology.natural (algebraMap k B) ei hi (scalar_commute k B ei)
    ej hj (scalar_commute k B ej) _ X n
end LittleFinitistic.LeftVertexHomology

end

end OAI

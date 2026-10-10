import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageCoordinateMaps
import OAI.GroupTheory.SimpleAmenable.Homology.ReducedTensorFinite

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D E:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
  [Groupoid.{0} E] [MonoidalCategory E] [SymmetricCategory E]
variable (F:C⥤D) (G:D⥤E) [F.Braided] [G.Braided]
lemma barMap_comp : barMap (F⋙G)=barMap F≫barMap G := by
  ext n x
  change x ⋙ map (I:=Fin (n.unop.len+1)) (F⋙G)=(x⋙map F)⋙map G
  rw [map_comp]
  rfl
lemma bar₂Map_comp : bar₂Map (F⋙G)=bar₂Map F≫bar₂Map G := by
  ext n x
  exact congrArg (fun T => x ⋙ T)
    (map₂_comp (I:=Fin (n.unop.len+1)) (J:=Fin (n.unop.len+1)) F G)
end IntervalBar.Diagram
namespace BarFinitePower
noncomputable def powerTwoIso (X:SSet) : (power (Fin 2)).obj X ≅ X⊗X where
  hom := { app _ := ↾fun x => (x 0,x 1)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun x=>![x.1,x.2]
           naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; funext i; fin_cases i <;> rfl }
  hom_inv_id := by apply NatTrans.ext;funext p;apply ConcreteCategory.hom_ext;intro x;funext i;fin_cases i <;> rfl
  inv_hom_id := by ext p x <;> rfl
noncomputable def powerOneIso (X:SSet) : (power (Fin 1)).obj X ≅ X where
  hom := evaluate _ _ 0
  inv := { app _ := ↾fun x _=>x
           naturality _ _ _ := rfl }
  hom_inv_id := by apply NatTrans.ext;funext p;apply ConcreteCategory.hom_ext;intro x;funext i;exact congrArg x (Subsingleton.elim _ _)
  inv_hom_id := by ext p x; rfl
end BarFinitePower

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialFirstFinite

attribute [local instance 1200] Submodule.module
universe u
variable {R:Type u} [CommRing R]
variable (T:SimplicialObject (ModuleCat.{u} R))
abbrev K := AlternatingFaceMapComplex.obj T
noncomputable def outer : T.obj (op ⦋2⦌) →ₗ[R] (T.obj (op ⦋1⦌) × T.obj (op ⦋1⦌)) :=
  (T.δ (0:Fin 3)).hom.prod (T.δ (2:Fin 3)).hom
noncomputable def sec : (T.obj (op ⦋1⦌) × T.obj (op ⦋1⦌)) →ₗ[R] T.obj (op ⦋2⦌) :=
  (T.σ (0:Fin 2)).hom.comp (LinearMap.fst R _ _) +
  (T.σ (1:Fin 2)).hom.comp (LinearMap.snd R _ _)
variable (h0:IsZero (T.obj (op ⦋0⦌)))
include h0
lemma sigma_zero_two : T.σ (0:Fin 2) ≫ T.δ (2:Fin 3)=0 := by
  change T.σ (Fin.castSucc (0:Fin 1)) ≫ T.δ (Fin.succ (1:Fin 2))=0
  rw [T.δ_comp_σ_of_gt (by decide)]
  rw [h0.eq_zero_of_tgt (T.δ (1:Fin 2)),zero_comp]
lemma sigma_one_zero : T.σ (1:Fin 2) ≫ T.δ (0:Fin 3)=0 := by
  change T.σ (Fin.succ (0:Fin 1)) ≫ T.δ (Fin.castSucc (0:Fin 2))=0
  rw [T.δ_comp_σ_of_le (by decide)]
  rw [h0.eq_zero_of_tgt (T.δ (0:Fin 2)),zero_comp]
lemma outer_sec : (outer T).comp (sec T)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change (T.δ (0:Fin 3)) ((T.σ (0:Fin 2)) x.1+(T.σ (1:Fin 2)) x.2)=x.1
    rw [map_add]
    change (T.σ (0:Fin 2)≫T.δ (0:Fin 3)) x.1+(T.σ (1:Fin 2)≫T.δ (0:Fin 3)) x.2=x.1
    rw [T.δ_comp_σ_self' (i:=(0:Fin 2)) (j:=(0:Fin 3)) rfl,sigma_one_zero T h0]
    simp
  · change (T.δ (2:Fin 3)) ((T.σ (0:Fin 2)) x.1+(T.σ (1:Fin 2)) x.2)=x.2
    rw [map_add]
    change (T.σ (0:Fin 2)≫T.δ (2:Fin 3)) x.1+(T.σ (1:Fin 2)≫T.δ (2:Fin 3)) x.2=x.2
    rw [sigma_zero_two T h0,T.δ_comp_σ_succ' (i:=(1:Fin 2)) (j:=(2:Fin 3)) rfl]
    simp
omit h0 in
lemma d21 : (K T).d 2 1=T.δ (0:Fin 3)-T.δ (1:Fin 3)+T.δ (2:Fin 3) := by
  simp [K,AlternatingFaceMapComplex.obj_d_eq,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc]
lemma d10 : (K T).d 1 0=0 := h0.eq_zero_of_tgt _
lemma sigma_d21 (i:Fin 2) : T.σ i ≫ (K T).d 2 1=0 := by
  rw [d21,Preadditive.comp_add,Preadditive.comp_sub]
  fin_cases i
  · change T.σ (0:Fin 2)≫T.δ (0:Fin 3)-T.σ (0:Fin 2)≫T.δ (1:Fin 3)+T.σ (0:Fin 2)≫T.δ (2:Fin 3)=0
    rw [T.δ_comp_σ_self' (i:=(0:Fin 2)) (j:=(0:Fin 3)) rfl,T.δ_comp_σ_succ' (i:=(0:Fin 2)) (j:=(1:Fin 3)) rfl,sigma_zero_two T h0,sub_self,add_zero]
  · change T.σ (1:Fin 2)≫T.δ (0:Fin 3)-T.σ (1:Fin 2)≫T.δ (1:Fin 3)+T.σ (1:Fin 2)≫T.δ (2:Fin 3)=0
    rw [sigma_one_zero T h0,T.δ_comp_σ_self' (i:=(1:Fin 2)) (j:=(1:Fin 3)) rfl,T.δ_comp_σ_succ' (i:=(1:Fin 2)) (j:=(2:Fin 3)) rfl]
    abel
lemma boundary_sec : (ConcreteHomology.boundary (K T) 1).comp (sec T)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change (K T).d 2 1 ((T.σ (0:Fin 2)) z.1+(T.σ (1:Fin 2)) z.2)=0
  rw [map_add]
  change (T.σ (0:Fin 2)≫(K T).d 2 1) z.1+(T.σ (1:Fin 2)≫(K T).d 2 1) z.2=0
  rw [sigma_d21 T h0,sigma_d21 T h0]
  simp
lemma boundary_finite [Module.Finite R (LinearMap.ker (outer T))] :
    Module.Finite R (LinearMap.range (ConcreteHomology.boundary (K T) 1)) := by
  let f := (ConcreteHomology.boundary (K T) 1).rangeRestrict.comp (LinearMap.ker (outer T)).subtype
  apply Module.Finite.of_surjective f
  rintro ⟨y,x,rfl⟩
  change ↑(T.obj (op ⦋2⦌)) at x
  refine ⟨⟨x-sec T (outer T x),?_⟩,?_⟩
  · change outer T (x-sec T (outer T x))=0
    rw [map_sub,show outer T (sec T (outer T x))=outer T x from
      congrArg (fun t => t (outer T x)) (outer_sec T h0),sub_self]
  · apply Subtype.ext
    change ConcreteHomology.boundary (K T) 1 (x-sec T (outer T x))=ConcreteHomology.boundary (K T) 1 x
    erw [map_sub,show ConcreteHomology.boundary (K T) 1 (sec T (outer T x))=0 from
      congrArg (fun t => t (outer T x)) (boundary_sec T h0),sub_zero]
lemma finite_one [Module.Finite R (LinearMap.ker (outer T))]
    [Module.Finite R ((K T).homology 1)] : Module.Finite R (T.obj (op ⦋1⦌)) := by
  have : Module.Finite R (ConcreteHomology.H (K T) 1) :=
    Module.Finite.equiv (ConcreteHomology.iso (K T) 1).toLinearEquiv
  have : Module.Finite R (LinearMap.range (ConcreteHomology.boundary (K T) 1)) := boundary_finite T h0
  have : Module.Finite R (ConcreteHomology.Cycles (K T) 1) := by
    apply Module.Finite.of_submodule_quotient (LinearMap.range (ConcreteHomology.boundary (K T) 1))
  exact Module.Finite.of_surjective (ConcreteHomology.Cycles (K T) 1).subtype (by
    intro x
    exact ⟨⟨x,by change (K T).d 1 0 x=0; rw [d10 T h0]; rfl⟩,rfl⟩)
end SimplicialFirstFinite

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open FreeChains

attribute [local instance 1200] Submodule.module Prod.instModule
variable (X:I ⥤ SSet)
noncomputable def segalTwo : X.obj (op ⦋2⦌) ⟶ X.obj (op ⦋1⦌) ⊗ X.obj (op ⦋1⦌) :=
  CartesianMonoidalCategory.lift (X.map (SimplexCategory.δ (0:Fin 3)).op) (X.map (SimplexCategory.δ (2:Fin 3)).op)
noncomputable def segalKernelMap (q:ℕ) :
    LinearMap.ker (SimplicialFirstFinite.outer (X⋙SSet.homologyFunctor Z q)) →ₗ[ℤ]
      LinearMap.ker (ConnectedProduct.projection (X.obj (op ⦋1⦌)) (X.obj (op ⦋1⦌)) q).hom :=
  ((SSet.homologyMap (segalTwo X) Z q).hom.comp
    (LinearMap.ker (SimplicialFirstFinite.outer (X⋙SSet.homologyFunctor Z q))).subtype).codRestrict _ (by
      intro x
      change ConnectedProduct.projection _ _ q (SSet.homologyMap (segalTwo X) Z q x.val)=0
      apply (ModuleCat.biprodIsoProd _ _).toLinearEquiv.injective
      simp only [map_zero]
      apply Prod.ext
      · change (SSet.homologyMap (segalTwo X) Z q ≫ ConnectedProduct.projection _ _ q ≫ biprod.fst) x.val=0
        simp only [ConnectedProduct.projection,biprod.lift_fst,←SSet.homologyMap_comp,
          segalTwo,CartesianMonoidalCategory.lift_fst]
        exact congrArg Prod.fst x.property
      · change (SSet.homologyMap (segalTwo X) Z q ≫ ConnectedProduct.projection _ _ q ≫ biprod.snd) x.val=0
        simp only [ConnectedProduct.projection,biprod.lift_snd,←SSet.homologyMap_comp,
          segalTwo,CartesianMonoidalCategory.lift_snd]
        exact congrArg Prod.snd x.property)
lemma segalKernelMap_injective (q:ℕ) [IsIso (SSet.homologyMap (segalTwo X) Z q)] :
    Function.Injective (segalKernelMap X q) := by
  intro x y h
  apply Subtype.ext
  exact (asIso (SSet.homologyMap (segalTwo X) Z q)).toLinearEquiv.injective (congrArg Subtype.val h)
lemma outer_kernel_finite (q:ℕ) [(X.obj (op ⦋1⦌)).IsConnected]
    [IsIso (SSet.homologyMap (segalTwo X) Z q)]
    (hf:∀i,i<q → Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z i : A)) :
    Module.Finite ℤ (LinearMap.ker (SimplicialFirstFinite.outer (X⋙SSet.homologyFunctor Z q))) := by
  have := ConnectedProduct.finite_projection_kernel (X.obj (op ⦋1⦌)) (X.obj (op ⦋1⦌)) q hf hf
  exact Module.Finite.of_injective (segalKernelMap X q) (segalKernelMap_injective X q)
end SimplicialDiagonal

end OAI

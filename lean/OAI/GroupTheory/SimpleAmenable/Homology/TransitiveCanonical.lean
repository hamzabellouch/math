import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TransitiveInduction
import OAI.GroupTheory.SimpleAmenable.Simplicial.ConjugationNatural

namespace OAI

open CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

lemma pointMap_factorization (x : X) (ht : ∀y : X, ∃g : G, g • x=y) :
    pointMap (G:=G) x =
      CanonicalShapiro.indUnit (MulAction.stabilizer G x).subtype
        (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≫
      (Rep.resFunctor.{0,0,0,0} (MulAction.stabilizer G x).subtype).map (iso x ht).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change Finsupp.single x z =
    toPermutation x ((CanonicalShapiro.indUnit _ _).hom z)
  rw [CanonicalShapiro.indUnit_apply, toPermutation_mk]
  simp
lemma isIso_map_pointMap (x : X) (ht : ∀y : X, ∃g : G, g • x=y) (q : ℕ) :
    IsIso (groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q) := by
  rw [pointMap_factorization x ht]
  have hn : groupHomology.map (MulAction.stabilizer G x).subtype
      (CanonicalShapiro.indUnit _ (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≫
       (Rep.resFunctor.{0,0,0,0} (MulAction.stabilizer G x).subtype).map (iso x ht).hom) q =
      groupHomology.map (MulAction.stabilizer G x).subtype
        (CanonicalShapiro.indUnit _ (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ)) q ≫
      (groupHomology.functor ℤ G q).map (iso x ht).hom :=
    groupHomology.map_comp (C:=Rep.of (permutationRep (G:=G) (X:=X)))
      (MulAction.stabilizer G x).subtype (MonoidHom.id G)
      (CanonicalShapiro.indUnit _ (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ))
      (iso x ht).hom q
  rw [hn]
  have first := CanonicalShapiro.isIso_map_indUnit (MulAction.stabilizer G x)
    (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) q
  have second : IsIso ((groupHomology.functor ℤ G q).map (iso x ht).hom) := inferInstance
  have composite := IsIso.comp_isIso' first second
  exact composite

noncomputable def equivariantMap (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) :
    Rep.of (permutationRep (G:=G) (X:=X)) ⟶
      Rep.of (permutationRep (G:=G) (X:=Y)) :=
  Rep.ofHom ⟨Finsupp.lmapDomain ℤ ℤ f, by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    simp [permutationRep, hf]⟩

@[simp] lemma equivariantMap_single (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x)
    (x : X) (z : ℤ) : (equivariantMap f hf).hom (Finsupp.single x z) =
      Finsupp.single (f x) z := by
  simp [equivariantMap]

def stabilizerMap (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) (x : X) :
    MulAction.stabilizer G x →* MulAction.stabilizer G (f x) :=
  (MulAction.stabilizer G x).inclusion (by
    intro g hg
    change g • f x=f x
    rw [← hf, hg])

noncomputable def trivialMap {K L : Type} [Group K] [Group L] (f : K →* L) :
    Rep.trivial ℤ K ℤ ⟶ Rep.res f (Rep.trivial ℤ L ℤ) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
lemma pointMap_natural (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) (x : X) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q ≫
      (groupHomology.functor ℤ G q).map (equivariantMap f hf) =
    groupHomology.map (A:=Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) (B:=Rep.trivial ℤ (MulAction.stabilizer G (f x)) ℤ) (stabilizerMap f hf x) (trivialMap (stabilizerMap f hf x)) q ≫
      groupHomology.map (MulAction.stabilizer G (f x)).subtype (pointMap (f x)) q := by
  rw [groupHomology.functor_map]
  erw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (equivariantMap f hf).hom (Finsupp.single x z) = Finsupp.single (f x) z
    exact equivariantMap_single f hf x z

lemma isIso_map_trivial_H0 {K L : Type} [Group K] [Group L] (f : K →* L) :
    IsIso (groupHomology.map f (trivialMap f) 0) := by
  have he : (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ K ℤ)).inv ≫
      groupHomology.map f (trivialMap f) 0 =
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ L ℤ)).inv := by
    rw [groupHomology.H0IsoOfIsTrivial_inv_eq_π,
      groupHomology.H0π_comp_map, groupHomology.H0IsoOfIsTrivial_inv_eq_π]
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  exact IsIso.of_isIso_fac_left he
lemma map_equivariant_eq_of_centralizer
    (f₀ f₁ : X → Y) (h₀ : ∀g : G,∀x,f₀ (g • x)=g • f₀ x)
    (h₁ : ∀g : G,∀x,f₁ (g • x)=g • f₁ x)
    (x : X) (ht : ∀y : X, ∃g : G,g • x=y) (c : G)
    (hc : ∀h : MulAction.stabilizer G x,c*h.val=h.val*c)
    (hx : c • f₀ x=f₁ x) (q : ℕ) :
    (groupHomology.functor ℤ G q).map (equivariantMap f₁ h₁) =
      (groupHomology.functor ℤ G q).map (equivariantMap f₀ h₀) := by
  let := isIso_map_pointMap x ht q
  apply (cancel_epi (groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q)).1
  rw [groupHomology.functor_map, groupHomology.functor_map]
  erw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply HomologyConjugation.map_eq_of_centralizer _ _ _ c hc
  intro z
  change (equivariantMap f₁ h₁).hom (Finsupp.single x z) =
    permutationRep c ((equivariantMap f₀ h₀).hom (Finsupp.single x z))
  rw [equivariantMap_single, equivariantMap_single, permutationRep_single, hx]
lemma isIso_map_equivariant_H0 (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x)
    (x : X) (htx : ∀y:X,∃g:G,g • x=y)
    (hty : ∀y:Y,∃g:G,g • f x=y) :
    IsIso ((groupHomology.functor ℤ G 0).map (equivariantMap f hf)) := by
  have sourceIso := isIso_map_pointMap x htx 0
  have targetIso := isIso_map_pointMap (f x) hty 0
  have trivialIso := isIso_map_trivial_H0 (stabilizerMap f hf x)
  have composite := IsIso.comp_isIso' trivialIso targetIso
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ sourceIso composite
    (pointMap_natural f hf x 0)

end SimpleAmenable.TransitiveInduction

end OAI

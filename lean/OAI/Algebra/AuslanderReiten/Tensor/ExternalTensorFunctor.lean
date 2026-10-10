import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorProjective
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def mapHom {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') :
    moduleObject k A B M N ⟶ moduleObject k A B M' N' :=
  ModuleCat.ofHom (X := moduleObject k A B M N) (Y := moduleObject k A B M' N')
    (map k A B f.hom g.hom)

@[simp] theorem mapHom_id (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    mapHom k A B (𝟙 M) (𝟙 N) = 𝟙 (moduleObject k A B M N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N) w = w
  simp

@[simp] theorem mapHom_comp {M M' M'' : ModuleCat.{u} A} {N N' N'' : ModuleCat.{u} B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    mapHom k A B (f ≫ f') (g ≫ g') = mapHom k A B f g ≫ mapHom k A B f' g' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map ((f'.hom.comp f.hom).restrictScalars k)
      ((g'.hom.comp g.hom).restrictScalars k) w =
    TensorProduct.map (f'.hom.restrictScalars k) (g'.hom.restrictScalars k)
      (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) w)
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rfl

theorem mapHom_add_left {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f f' : M ⟶ M') (g : N ⟶ N') :
    mapHom k A B (f+f') g = mapHom k A B f g + mapHom k A B f' g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map ((f.hom+f'.hom).restrictScalars k) (g.hom.restrictScalars k) w =
    TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) w +
      TensorProduct.map (f'.hom.restrictScalars k) (g.hom.restrictScalars k) w
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul x y => exact TensorProduct.add_tmul _ _ _

theorem mapHom_add_right {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g g' : N ⟶ N') :
    mapHom k A B f (g+g') = mapHom k A B f g + mapHom k A B f g' := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (f.hom.restrictScalars k) ((g.hom+g'.hom).restrictScalars k) w =
    TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k) w +
      TensorProduct.map (f.hom.restrictScalars k) (g'.hom.restrictScalars k) w
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul x y => exact TensorProduct.tmul_add _ _ _

def rightFunctor (M : ModuleCat.{u} A) : ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) where
  obj N := moduleObject k A B M N
  map f := mapHom k A B (𝟙 M) f
  map_id N := mapHom_id k A B M N
  map_comp f g := by simpa only [Category.id_comp] using mapHom_comp k A B (𝟙 M) (𝟙 M) f g

instance (M : ModuleCat.{u} A) : (rightFunctor k A B M).Additive where
  map_add := by intros; exact mapHom_add_right k A B (𝟙 M) _ _

def bifunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) where
  obj := rightFunctor k A B
  map f :=
    { app := fun N => mapHom k A B f (𝟙 N)
      naturality N N' g := by
        change mapHom k A B (𝟙 _) g ≫ mapHom k A B f (𝟙 _) =
          mapHom k A B f (𝟙 _) ≫ mapHom k A B (𝟙 _) g
        simp only [← mapHom_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact mapHom_id k A B M N
  map_comp f g := by
    apply NatTrans.ext
    funext N
    change mapHom k A B (f ≫ g) (𝟙 N) = mapHom k A B f (𝟙 N) ≫ mapHom k A B g (𝟙 N)
    simpa only [Category.id_comp] using mapHom_comp k A B f g (𝟙 N) (𝟙 N)

instance : (bifunctor k A B).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext L
    exact mapHom_add_left k A B f g (𝟙 L)

instance (M : ModuleCat.{u} A) : ((bifunctor k A B).obj M).Additive :=
  inferInstanceAs ((rightFunctor k A B M).Additive)

end ArExplicit.ExternalTensor

end

end OAI

import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageCoordinateMaps

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower
section
open FreeChains

def LowFinite (X:SSet) : Prop :=
  (∀j:ℕ,j≤5 → Module.Finite ℤ (X.homology Z j : A)) ∧
  (∀j:ℕ,0<j → j<3 → IsZero (X.homology Z j))
namespace LowFinite
variable {X Y:SSet}
lemma of_iso (e:X≅Y) (h:LowFinite Y) : LowFinite X := by
  constructor
  · intro j hj
    have := h.1 j hj
    exact (Module.Finite.equiv_iff ((SSet.homologyFunctor Z j).mapIso e).symm.toLinearEquiv).mp (h.1 j hj)
  · intro j hj h3
    exact IsZero.of_iso (h.2 j hj h3) ((SSet.homologyFunctor Z j).mapIso e)
lemma one : LowFinite ConnectedProduct.one := by
  constructor
  · intro j hj
    by_cases h:j=0
    · subst j; exact homology_zero_finite _
    · have := ModuleCat.isZero_iff_subsingleton.mp (ConnectedProduct.one_homology_zero j h)
      infer_instance
  · intro j hj h3
    exact ConnectedProduct.one_homology_zero j (by omega)
lemma projection_isIso [X.IsConnected] [Y.IsConnected] (hX:LowFinite X) (hY:LowFinite Y)
    (j:ℕ) (hj:0<j) (hj5:j≤5) : IsIso (ConnectedProduct.projection X Y j) := by
  have := hX.1 j hj5
  apply ConnectedProduct.projection_isIso X Y 3 3 j hj (by omega)
  · intro i hi h3; exact homology_isZero_complex X i (hX.2 i hi h3)
  · intro i hi h3; exact homology_isZero_complex Y i (hY.2 i hi h3)
  · intro i hi
    have := hY.1 i (hi.trans hj5)
    exact homology_finite_complex Y i
lemma tensor [X.IsConnected] [Y.IsConnected] (hX:LowFinite X) (hY:LowFinite Y) : LowFinite (X⊗Y) := by
  constructor
  · intro j hj
    by_cases hz:j=0
    · subst j; exact homology_zero_finite _
    · have := projection_isIso hX hY j (by omega) hj
      have := hX.1 j hj
      have := hY.1 j hj
      have : Module.Finite ℤ (X.homology Z j ⊞ Y.homology Z j : A) := ConnectedProduct.finite_biprod _ _
      exact Module.Finite.equiv (asIso (ConnectedProduct.projection X Y j)).symm.toLinearEquiv
  · intro j hj h3
    have := projection_isIso hX hY j hj (by omega)
    exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr ⟨hX.2 j hj h3,hY.2 j hj h3⟩)
      (asIso (ConnectedProduct.projection X Y j))
lemma fin [X.IsConnected] (hX:LowFinite X) (s:ℕ) : LowFinite ((power (Fin s)).obj X) := by
  induction s with
  | zero => exact of_iso (finZeroIso X) one
  | succ s ih => exact of_iso (finSuccIso X s) (tensor hX ih)
lemma power [X.IsConnected] (hX:LowFinite X) (κ:Type) [Finite κ] : LowFinite ((BarFinitePower.power κ).obj X) := by
  let := Fintype.ofFinite κ
  exact of_iso (reindexIso X (Fintype.equivFin κ)) (fin hX _)
end LowFinite
end

section
open FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable (κ:Type) (X:SSet) (j:ℕ)
noncomputable def coordinates : ((power κ).obj X).homology Z j ⟶ ModuleCat.of ℤ (κ → (X.homology Z j : A)) :=
  ModuleCat.ofHom (LinearMap.pi (fun k => (SSet.homologyMap (evaluate κ X k) Z j).hom))
@[reassoc (attr := simp)] lemma coordinates_evaluate (k:κ) :
    coordinates κ X j ≫ ModuleCat.ofHom (LinearMap.proj k) = SSet.homologyMap (evaluate κ X k) Z j := rfl
lemma modulePi_hom_ext {κ:Type} {M B:A} {f g:B ⟶ ModuleCat.of ℤ (κ → M)}
    (h:∀i,f ≫ ModuleCat.ofHom (LinearMap.proj i)=g ≫ ModuleCat.ofHom (LinearMap.proj i)) : f=g := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext i
  exact congrArg (fun f => f x) (h i)
variable (M:A)
noncomputable def vectorSplit (s:ℕ) : (Fin (s+1) → M) ≃ₗ[ℤ] M × (Fin s → M) where
  toFun x := (x 0,fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by funext i; cases i using Fin.cases <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def coordinateSplit (s:ℕ) : ModuleCat.of ℤ (Fin (s+1) → M) ≅ M ⊞ ModuleCat.of ℤ (Fin s → M) :=
  (vectorSplit M s).toModuleIso ≪≫ (ModuleCat.biprodIsoProd M (ModuleCat.of ℤ (Fin s → M))).symm
@[reassoc (attr := simp)] lemma coordinateSplit_fst (s:ℕ) :
    (coordinateSplit M s).hom ≫ biprod.fst = ModuleCat.ofHom (LinearMap.proj (0:Fin (s+1))) := by
  simp only [coordinateSplit,Iso.trans_hom,Iso.symm_hom,Category.assoc,ModuleCat.biprodIsoProd_inv_comp_fst]
  rfl
@[reassoc (attr := simp)] lemma coordinateSplit_snd_proj (s:ℕ) (i:Fin s) :
    (coordinateSplit M s).hom ≫ biprod.snd ≫ ModuleCat.ofHom (LinearMap.proj i) =
      ModuleCat.ofHom (LinearMap.proj i.succ) := by
  simp only [coordinateSplit,Iso.trans_hom,Iso.symm_hom,Category.assoc]
  have h := congrArg (fun f => f ≫ (ModuleCat.ofHom (LinearMap.proj i) : ModuleCat.of ℤ (Fin s→M) ⟶ M))
    (ModuleCat.biprodIsoProd_inv_comp_snd M (ModuleCat.of ℤ (Fin s→M)))
  simp only [Category.assoc] at h
  rw [h]
  rfl
lemma coordinates_fin_succ (s:ℕ) :
    coordinates (Fin (s+1)) X j ≫ (coordinateSplit (X.homology Z j) s).hom =
      SSet.homologyMap (finSuccIso X s).hom Z j ≫
        ConnectedProduct.projection X ((power (Fin s)).obj X) j ≫
          biprod.map (𝟙 _) (coordinates (Fin s) X j) := by
  apply biprod.hom_ext
  · simp only [Category.assoc,coordinateSplit_fst,coordinates_evaluate,biprod.map_fst,
      Category.comp_id,ConnectedProduct.projection,biprod.lift_fst,←SSet.homologyMap_comp]
    rfl
  · apply modulePi_hom_ext
    intro i
    simp only [Category.assoc,coordinateSplit_snd_proj,coordinates_evaluate,
      biprod.map_snd_assoc,ConnectedProduct.projection,biprod.lift_snd_assoc,←SSet.homologyMap_comp]
    rfl
end
open FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable (X:SSet) [X.IsConnected] (hX:LowFinite X)
include hX in
lemma coordinates_fin_isIso (s j:ℕ) (hj:0<j) (hj5:j≤5) : IsIso (coordinates (Fin s) X j) := by
  induction s with
  | zero =>
    have hz : IsZero (((power (Fin 0)).obj X).homology Z j) :=
      IsZero.of_iso (ConnectedProduct.one_homology_zero j (by omega))
        ((SSet.homologyFunctor Z j).mapIso (finZeroIso X))
    exact hz.isIso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) _
  | succ s ih =>
    have := ih
    have := LowFinite.projection_isIso hX (hX.fin s) j hj hj5
    have : IsIso (biprod.map (𝟙 (X.homology Z j)) (coordinates (Fin s) X j)) := by
      change IsIso (biprod.mapIso (Iso.refl _) (asIso (coordinates (Fin s) X j))).hom
      infer_instance
    have : IsIso (coordinates (Fin (s+1)) X j ≫ (coordinateSplit (X.homology Z j) s).hom) := by
      rw [coordinates_fin_succ]
      infer_instance
    exact (isIso_comp_right_iff _ (coordinateSplit (X.homology Z j) s).hom).mp inferInstance
noncomputable def coefficientReindex {κ ι:Type} (e:κ≃ι) (M:A) :
    ModuleCat.of ℤ (κ→M) ≅ ModuleCat.of ℤ (ι→M) :=
  (show (κ→M) ≃ₗ[ℤ] (ι→M) from {
    toFun f i := f (e.symm i)
    invFun f k := f (e k)
    left_inv f := by funext k; exact congrArg f (e.symm_apply_apply k)
    right_inv f := by funext i; exact congrArg f (e.apply_symm_apply i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }).toModuleIso
omit [X.IsConnected] in
lemma coordinates_reindex {κ ι:Type} (e:κ≃ι) (j:ℕ) :
    coordinates κ X j ≫ (coefficientReindex e (X.homology Z j)).hom =
      SSet.homologyMap (reindexIso X e).hom Z j ≫ coordinates ι X j := by
  apply modulePi_hom_ext; intro i
  have he : (coefficientReindex e (X.homology Z j)).hom ≫ ModuleCat.ofHom (LinearMap.proj i)=
      ModuleCat.ofHom (LinearMap.proj (e.symm i)) := rfl
  rw [Category.assoc,he,coordinates_evaluate,Category.assoc,coordinates_evaluate,←SSet.homologyMap_comp]
  rfl
include hX in

lemma coordinates_isIso (κ:Type) [Finite κ] (j:ℕ) (hj:0<j) (hj5:j≤5) :
    IsIso (coordinates κ X j) := by
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  have := coordinates_fin_isIso X hX (Fintype.card κ) j hj hj5
  have : IsIso (coordinates κ X j ≫ (coefficientReindex e (X.homology Z j)).hom) := by
    rw [coordinates_reindex]
    infer_instance
  exact (isIso_comp_right_iff _ (coefficientReindex e (X.homology Z j)).hom).mp inferInstance
end BarFinitePower

end OAI

import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ConeHomology
import OAI.GroupTheory.SimpleAmenable.Homology.ConnectedProduct
import OAI.GroupTheory.SimpleAmenable.Simplicial.SimplicialConnectedProduct

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ConnectedProduct
open FreeChains AugmentedSplit

abbrev one : SSet := (Functor.const SimplexCategoryᵒᵖ).obj PUnit
lemma one_homology_zero (n : ℕ) (hn : n≠0) : IsZero (one.homology Z n) := by
  let V := (sigmaConst.obj Z).obj PUnit
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const V).homotopyEquiv
  have hz : IsZero (((ChainComplex.single₀ A).obj V).homology n) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact HomologicalComplex.isZero_single_obj_X c 0 V n hn
  let ei : one.chainComplex Z ≅ AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj V) :=
    (alternatingFaceMapComplex A).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ PUnit (sigmaConst.obj Z))
  exact IsZero.of_iso hz (((homologyFunctor A c n).mapIso ei) ≪≫ e.toHomologyIso n)
lemma const_homology_zero {X Y : SSet} (y : Y.obj (op ⦋0⦌)) (n : ℕ) (hn : n≠0) :
    SSet.homologyMap (SSet.const (X:=X) y) Z n = 0 := by
  have hh : SSet.const (X:=X) y = SSet.const (X:=X) (Y:=one) PUnit.unit ≫ SSet.const y := by simp
  rw [hh,SSet.homologyMap_comp]
  have hz := one_homology_zero n hn
  rw [hz.eq_of_src (SSet.homologyMap (SSet.const (X:=one) y) Z n) 0,comp_zero]
variable (X Y : SSet)
noncomputable def diagonalProductIso : EilenbergZilber.diag ⋙ ProductChains.product X Y ≅ X⊗Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
noncomputable def projection (n : ℕ) : (X⊗Y).homology Z n ⟶ X.homology Z n ⊞ Y.homology Z n :=
  biprod.lift (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n)
    (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n)
noncomputable def inclusion (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) (n : ℕ) :
    X.homology Z n ⊞ Y.homology Z n ⟶ (X⊗Y).homology Z n :=
  biprod.desc (SSet.homologyMap (pairLeft X Y y) Z n) (SSet.homologyMap (pairRight X Y x) Z n)
lemma inclusion_projection (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) (n : ℕ) (hn : n≠0) :
    inclusion X Y x y n ≫ projection X Y n=𝟙 _ := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  all_goals simp only [inclusion,projection,Category.assoc,biprod.inl_desc_assoc,
    biprod.inr_desc_assoc,biprod.lift_fst,biprod.lift_snd,biprod.inl_fst,biprod.inl_snd,
    biprod.inr_fst,biprod.inr_snd,Category.comp_id,←SSet.homologyMap_comp]
  all_goals simp [pairLeft,pairRight,CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd,const_homology_zero _ n hn]
lemma finite_biprod {R : Type} [CommRing R] (M N : ModuleCat R)
    [Module.Finite R M] [Module.Finite R N] : Module.Finite R (M ⊞ N : ModuleCat R) :=
  Module.Finite.equiv (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv
lemma projection_isIso [X.IsConnected] [Y.IsConnected]
    (a b n : ℕ) (hn : 0<n) (hab : n<a+b)
    (hX : ∀ i, 0 < i → i < a → IsZero ((complex X).homology i))
    (hY : ∀ i, 0 < i → i < b → IsZero ((complex Y).homology i))
    (hf : ∀ i, i ≤ n → Module.Finite ℤ ((complex Y).homology i))
    [Module.Finite ℤ (X.homology Z n : A)] : IsIso (projection X Y n) := by
  have : Module.Finite ℤ (Y.homology Z n : A) := by
    apply (Module.Finite.equiv_iff ((homologyFunctor A c n).mapIso (complexIso Y)).symm.toLinearEquiv).mp
    exact hf n le_rfl
  let e := (SSet.homologyFunctor Z n).mapIso (diagonalProductIso X Y).symm ≪≫
    additiveIso X Y a b n hn hab hX hY hf
  have hsurj : Function.Surjective (projection X Y n).hom := by
    intro z
    refine ⟨inclusion X Y (point X) (point Y) n z,?_⟩
    exact congrArg (fun f => f z) (inclusion_projection X Y (point X) (point Y) n (by omega))
  have : Module.Finite ℤ (X.homology Z n ⊞ Y.homology Z n : A) :=
    finite_biprod _ _
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨IsNoetherian.injective_of_surjective_of_injective e.toLinearEquiv.toLinearMap
      (projection X Y n).hom e.toLinearEquiv.injective hsurj,hsurj⟩
end ConnectedProduct

end

end

end OAI

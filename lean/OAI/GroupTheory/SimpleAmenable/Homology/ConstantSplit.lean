import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.CanonicalProduct
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiniteSetMonoidal
import OAI.GroupTheory.SimpleAmenable.Homology.ProductNatural
import OAI.GroupTheory.SimpleAmenable.Homology.TensorJoint

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ProductChains
open FreeChains

variable {X Y W:SSet}
@[simp] lemma chainMap_id (X:SSet) : chainMap (𝟙 X)=𝟙 (complex X) := by
  unfold chainMap; simp [complex]; rfl
@[simp] lemma chainMap_comp (f:X⟶Y) (g:Y⟶W) : chainMap (f≫g)=chainMap f≫chainMap g := by
  unfold chainMap; simp; rfl
lemma chainMap_aug (f:X⟶Y) : chainMap f ≫ SimplicialAugment.aug Y = SimplicialAugment.aug X := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,SimplicialAugment.aug_f_zero]
  apply ModuleCat.free_hom_ext; intro x
  change SimplicialAugment.aug0 Y ((ModuleCat.free ℤ).map (f.app (op ⦋0⦌)) (ModuleCat.freeMk x)) = SimplicialAugment.aug0 X (ModuleCat.freeMk x)
  simp only [ModuleCat.free_map_apply]
  rw [SimplicialAugment.aug0_mk,SimplicialAugment.aug0_mk]
end ProductChains
namespace ConstantSplit
open FreeChains ProductChains

abbrev one := ConnectedProduct.one
noncomputable def aug (X:SSet) : complex X ⟶ complex one := chainMap (SSet.const (Y:=one) PUnit.unit)
noncomputable def sec (X:SSet) (x:X.obj (op ⦋0⦌)) : complex one ⟶ complex X := chainMap (SSet.const x)
lemma section_aug (X:SSet) (x:X.obj (op ⦋0⦌)) : sec X x ≫ aug X = 𝟙 (complex one) := by
  rw [sec,aug,←chainMap_comp]
  have he : (SSet.const (X:=one) x) ≫ SSet.const (Y:=one) PUnit.unit = 𝟙 one := by ext n z; rfl
  rw [he,chainMap_id]
noncomputable def sc (X:SSet) : ShortComplex (ChainComplex A ℕ) :=
  ShortComplex.mk (kernel.ι (aug X)) (aug X) (kernel.condition _)
noncomputable def splitting (X:SSet) (x:X.obj (op ⦋0⦌)) : (sc X).Splitting :=
  ShortComplex.Splitting.ofExactOfSection (sc X)
    ((sc X).exact_of_f_is_kernel (kernelIsKernel (aug X))) (sec X x) (section_aug X x)
      (by dsimp [sc]; infer_instance)
instance aug_iso (X:SSet) [X.IsConnected] : IsIso (homologyMap (aug X) 0) := by
  have oneConnected : one.IsConnected := {
    allEq := by
      intro first second
      obtain ⟨first,rfl⟩ := SSet.π₀.mk_surjective first
      obtain ⟨second,rfl⟩ := SSet.π₀.mk_surjective second
      exact congrArg SSet.π₀.mk (show first=second from PUnit.ext first second)
    nonempty := ⟨PUnit.unit⟩ }
  have he : homologyMap (aug X) 0 ≫ homologyMap (SimplicialAugment.aug one) 0 =
      homologyMap (SimplicialAugment.aug X) 0 := by
    rw [←homologyMap_comp]; exact congrArg (fun f => homologyMap f 0) (chainMap_aug _)
  have compositeIso : IsIso (homologyMap (aug X) 0 ≫ homologyMap (SimplicialAugment.aug one) 0) := by
    rw [he]; infer_instance
  exact (isIso_comp_right_iff _ (homologyMap (SimplicialAugment.aug one) 0)).mp inferInstance
lemma red_zero (X:SSet) [X.IsConnected] (a:ℕ)
    (hv : ∀ i, 0 < i → i < a → IsZero ((complex X).homology i)) :
    ∀ i, i < a → IsZero (((sc X).X₁).homology i) := by
  intro i hi
  let s := splitting X (ConnectedProduct.point X)
  have hz : homologyMap (sc X).f i=0 := by
    by_cases h:i=0
    · subst i
      change homologyMap (kernel.ι (aug X)) 0 = 0
      apply (cancel_mono (homologyMap (aug X) 0)).mp
      rw [←homologyMap_comp,kernel.condition,homologyMap_zero,zero_comp]
    · exact (hv i (by omega) hi).eq_of_tgt _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  have hh := congrArg (fun f => homologyMap f i) s.f_r
  rw [homologyMap_comp,homologyMap_id,hz,zero_comp] at hh
  exact hh.symm
instance red_flat (X:SSet) (i:ℕ) : Module.Flat ℤ (((sc X).X₁).X i) := by
  have hi : Function.Injective ((kernel.ι (aug X)).f i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have reducedTorsionFree : Module.IsTorsionFree ℤ (((sc X).X₁).X i) :=
    hi.moduleIsTorsionFree _ (fun r x => ((kernel.ι (aug X)).f i).hom.map_smul r x)
  infer_instance
end ConstantSplit

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains

variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
lemma projection_kernel_aux (a b n:ℕ) (hab:n<a+b)
    (hX:∀ i, 0 < i → i < a → IsZero ((complex X).homology i))
    (hY:∀ i, 0 < i → i < b → IsZero ((complex Y).homology i))
    (x:((X⊗Y).homology Z n : A)) (hx:projection X Y n x=0) : x=0 := by
  have hf : SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.fst : X.homology Z n ⊞ Y.homology Z n ⟶ X.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.fst) x=0 at h
    simpa only [projection,biprod.lift_fst] using h
  have hg : SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.snd : X.homology Z n ⊞ Y.homology Z n ⟶ Y.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.snd) x=0 at h
    simpa only [projection,biprod.lift_snd] using h
  let e := homologyIsoN X Y n
  have h1 : homologyMap (𝟙 (complex X)⊗ₘConstantSplit.aug Y) n (e.hom x)=0 := by
    have hn := homology_natural (𝟙 X) (SSet.const (X:=Y) (Y:=one) PUnit.unit) n
    rw [chainMap_id] at hn
    have he : (𝟙 X)⊗ₘ(SSet.const (X:=Y) (Y:=one) PUnit.unit) =
        CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN X one n).hom
      (SSet.homologyMap (pairLeft X one PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x)) = _ at hh
    simpa only [hf,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have h2 : homologyMap (ConstantSplit.aug X⊗ₘ𝟙 (complex Y)) n (e.hom x)=0 := by
    have hn := homology_natural (SSet.const (X:=X) (Y:=one) PUnit.unit) (𝟙 Y) n
    rw [chainMap_id] at hn
    have he : (SSet.const (X:=X) (Y:=one) PUnit.unit)⊗ₘ(𝟙 Y) =
        CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN one Y n).hom
      (SSet.homologyMap (pairRight one Y PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x)) = _ at hh
    simpa only [hg,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have hz : IsZero ((((ConstantSplit.sc X).X₁)⊗((ConstantSplit.sc Y).X₁)).homology n) :=
    TensorProductHomology.arbitrary_isZero _ _ a b n hab
      (ConstantSplit.red_zero X a hX) (ConstantSplit.red_zero Y b hY)
  have hh := ChainTensor.homology_joint_kernel (ConstantSplit.sc X) (ConstantSplit.sc Y)
    (ConstantSplit.splitting X (point X)) (ConstantSplit.splitting Y (point Y)) n hz (e.hom x) h1 h2
  exact e.toLinearEquiv.injective (hh.trans (map_zero e.toLinearEquiv).symm)

lemma projection_isIso_arbitrary (a b n:ℕ) (hn:0<n) (hab:n<a+b)
    (hX:∀ i, 0 < i → i < a → IsZero ((complex X).homology i))
    (hY:∀ i, 0 < i → i < b → IsZero ((complex Y).homology i)) :
    IsIso (projection X Y n) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply sub_eq_zero.mp
    apply projection_kernel_aux X Y a b n hab hX hY (x-y)
    rw [map_sub,h,sub_self]
  · intro z
    refine ⟨inclusion X Y (point X) (point Y) n z,?_⟩
    exact congrArg (fun f => f z) (inclusion_projection X Y (point X) (point Y) n (by omega))
end ConnectedProduct

end

end

end OAI

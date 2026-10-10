import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.CoefficientUCT

namespace OAI

section

section

open CategoryTheory Limits MonoidalCategory SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace ProductChains

open FreeChains
lemma sum_f {K L : ChainComplex A ℕ} {ι : Type} (s : Finset ι) (f : ι → (K ⟶ L)) (q : ℕ) :
    (∑ i∈s,f i).f q=∑ i∈s,(f i).f q := map_sum (HomologicalComplex.Hom.fAddMonoidHom q) f s
abbrev D := SimplexCategory × SimplexCategory
variable (X Y : SSet)
def product : Dᵒᵖ ⥤ Type where
  obj a := X.obj (op a.unop.1) × Y.obj (op a.unop.2)
  map f := ↾fun z => (X.map f.unop.1.op z.1,Y.map f.unop.2.op z.2)
  map_id _ := by ext z <;> simp
  map_comp f g := by ext z <;> simp

noncomputable def twoFree : HomologicalComplex₂ A c c :=
  AlternatingFaceMapComplex.obj (EilenbergZilber.bisimplicial (product X Y ⋙ ModuleCat.free ℤ) ⋙
    alternatingFaceMapComplex A)

noncomputable def freeIso : EilenbergZilber.twoComplex (product X Y) ≅ twoFree X Y :=
  (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerRight
      ((Functor.curry.mapIso (Functor.isoWhiskerLeft
        (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse
        (Functor.isoWhiskerLeft (product X Y) FreeChains.naturalIso))))
      (alternatingFaceMapComplex A))

noncomputable def rowIso (p : ℕ) :
    (TensorProductHomology.bicomplex (complex X) (complex Y)).X p ≅ (twoFree X Y).X p := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => Functor.Monoidal.μIso (ModuleCat.free ℤ) (X.obj (op ⦋p⦌)) (Y.obj (op ⦋q⦌))) ?_
  intro q q' h
  obtain rfl : q=q'+1 := h.symm
  change Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p⦌)) (Y.obj (op ⦋q'+1⦌)) ≫
      (AlternatingFaceMapComplex.obj ((EilenbergZilber.bisimplicial (product X Y ⋙ ModuleCat.free ℤ)).obj (op ⦋p⦌))).d (q'+1) q' =
    (tensorLeft ((ModuleCat.free ℤ).obj (X.obj (op ⦋p⦌)))).map ((AlternatingFaceMapComplex.obj (Y ⋙ ModuleCat.free ℤ)).d (q'+1) q') ≫
      Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p⦌)) (Y.obj (op ⦋q'⦌))
  simp only [AlternatingFaceMapComplex.obj_d_eq,
    Functor.map_sum,Functor.map_zsmul,Preadditive.sum_comp,Preadditive.zsmul_comp]
  refine (Preadditive.comp_sum _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro _ _
  refine (Preadditive.comp_zsmul _ _ _).trans ?_
  congr 1
  simp [EilenbergZilber.bisimplicial,product,SimplicialObject.δ]
  rfl

noncomputable def tensorIso :
    TensorProductHomology.bicomplex (complex X) (complex Y) ≅ twoFree X Y := by
  refine HomologicalComplex.Hom.isoOfComponents (rowIso X Y) ?_
  intro p p' h
  obtain rfl : p=p'+1 := h.symm
  apply HomologicalComplex.Hom.ext
  funext q
  change Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p'+1⦌)) (Y.obj (op ⦋q⦌)) ≫
      ((twoFree X Y).d (p'+1) p').f q =
    (tensorRight ((ModuleCat.free ℤ).obj (Y.obj (op ⦋q⦌)))).map ((complex X).d (p'+1) p') ≫
      Functor.LaxMonoidal.μ (ModuleCat.free ℤ) (X.obj (op ⦋p'⦌)) (Y.obj (op ⦋q⦌))
  simp only [twoFree,complex,AlternatingFaceMapComplex.obj_d_eq,
    sum_f,HomologicalComplex.zsmul_f_apply,
    Functor.map_sum,Functor.map_zsmul,Preadditive.sum_comp,Preadditive.zsmul_comp]
  refine (Preadditive.comp_sum _ _ _).trans ?_
  apply Finset.sum_congr rfl
  intro _ _
  refine (Preadditive.comp_zsmul _ _ _).trans ?_
  congr 1
  simp [EilenbergZilber.bisimplicial,product,SimplicialObject.δ]
  rfl

noncomputable def homologyIso (n : ℕ) :
    SSet.homology (EilenbergZilber.diag ⋙ product X Y) Z n ≅
      ((TensorProductHomology.bicomplex (complex X) (complex Y)).total c).homology n :=
  EilenbergZilber.homologyIso (product X Y) n ≪≫
    (homologyFunctor _ c n).mapIso
      (total.mapIso (freeIso X Y ≪≫ (tensorIso X Y).symm) c)

end ProductChains

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainTensor
open FreeChains
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

instance leftAdditive (K : ChainComplex A ℕ) : (tensorLeft K).Additive where
  map_add {L M} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro p q hpq
    change ιMapBifunctor K L (curriedTensor A) c p q n hpq ≫
        (mapBifunctorMap (𝟙 K) (f+g) (curriedTensor A) c).f n =
      ιMapBifunctor K L (curriedTensor A) c p q n hpq ≫
        ((mapBifunctorMap (𝟙 K) f (curriedTensor A) c).f n + (mapBifunctorMap (𝟙 K) g (curriedTensor A) c).f n)
    simp [Preadditive.comp_add]
instance rightAdditive (K : ChainComplex A ℕ) : (tensorRight K).Additive where
  map_add {L M} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro p q hpq
    change ιMapBifunctor L K (curriedTensor A) c p q n hpq ≫
        (mapBifunctorMap (f+g) (𝟙 K) (curriedTensor A) c).f n =
      ιMapBifunctor L K (curriedTensor A) c p q n hpq ≫
        ((mapBifunctorMap f (𝟙 K) (curriedTensor A) c).f n + (mapBifunctorMap g (𝟙 K) (curriedTensor A) c).f n)
    simp [Preadditive.comp_add]
noncomputable def leftDistrib (K L M : ChainComplex A ℕ) :
    K ⊗ (L ⊞ M) ≅ (K ⊗ L) ⊞ (K ⊗ M) := (tensorLeft K).mapBiprod L M
noncomputable def rightDistrib (K L M : ChainComplex A ℕ) :
    (K ⊞ L) ⊗ M ≅ (K ⊗ M) ⊞ (L ⊗ M) := (tensorRight M).mapBiprod K L
end ChainTensor

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace AugmentedSplit
open FreeChains
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

noncomputable abbrev U : ChainComplex A ℕ := 𝟙_ (ChainComplex A ℕ)
variable {K : ChainComplex A ℕ} (e : K ⟶ U) (s : U ⟶ K) (hs : s ≫ e=𝟙 U)
noncomputable abbrev red := kernel e
noncomputable def sc : ShortComplex (ChainComplex A ℕ) :=
  ShortComplex.mk (kernel.ι e) e (kernel.condition e)
noncomputable def splitting : (sc e).Splitting :=
  ShortComplex.Splitting.ofExactOfSection (sc e)
    ((sc e).exact_of_f_is_kernel (kernelIsKernel e)) s hs (by dsimp [sc]; infer_instance)
noncomputable def iso : K ≅ red e ⊞ U := (splitting e s hs).isoBinaryBiproduct

lemma flat [∀n,Module.Flat ℤ (K.X n)] (n : ℕ) : Module.Flat ℤ ((red e).X n) := by
  have hf : Function.Injective ((kernel.ι e).f n) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have : Module.IsTorsionFree ℤ ((red e).X n) :=
    hf.moduleIsTorsionFree _ (fun r x => ((kernel.ι e).f n).hom.map_smul r x)
  infer_instance

include s hs in
lemma finite (n : ℕ) [Module.Finite ℤ (K.homology n)] :
    Module.Finite ℤ ((red e).homology n) := by
  let i := homologyMap (kernel.ι e) n
  let r := homologyMap (splitting e s hs).r n
  have hi : Function.Injective i := by
    apply Function.LeftInverse.injective (f:=i) (g:=r)
    intro x
    have h : i ≫ r = 𝟙 _ := by
      change homologyMap (sc e).f n ≫ homologyMap (splitting e s hs).r n = _
      rw [←homologyMap_comp,(splitting e s hs).f_r,homologyMap_id]
      rfl
    exact congrArg (fun f => f x) h
  exact Module.Finite.of_injective i.hom hi

lemma uni_isZero (n : ℕ) (hn : n≠0) : IsZero (U.homology n) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact HomologicalComplex.isZero_single_obj_X c 0 _ n hn

noncomputable def homologyIso (n : ℕ) (hn : n≠0) : K.homology n ≅ (red e).homology n :=
  (homologyFunctor A c n).mapIso (iso e s hs) ≪≫
    (homologyFunctor A c n).mapBiprod _ _ ≪≫ (isoBiprodZero (uni_isZero n hn)).symm

include s hs in
lemma vanishing (a : ℕ) (h0 : IsZero ((red e).homology 0))
    (hK : ∀ i, 0 < i → i < a → IsZero (K.homology i)) :
    ∀ i, i < a → IsZero ((red e).homology i) := by
  intro i hi
  by_cases h : i=0
  · simpa [h] using h0
  · exact IsZero.of_iso (hK i (by omega) hi) (homologyIso e s hs i h).symm
end AugmentedSplit

end

end

end OAI

import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.EZNatural
import OAI.GroupTheory.SimpleAmenable.Homology.ProductChains

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace ProductChains
open FreeChains

variable {X Y X' Y':SSet}
def map (f:X⟶X') (g:Y⟶Y') : product X Y ⟶ product X' Y' where
  app d := ↾fun z => (f.app (op d.unop.1) z.1,g.app (op d.unop.2) z.2)
  naturality _ _ h := by ext z; exact Prod.ext (congrArg (fun k => k z.1) (f.naturality h.unop.1.op)) (congrArg (fun k => k z.2) (g.naturality h.unop.2.op))
noncomputable def chainMap (f:X⟶X') : complex X ⟶ complex X' :=
  (alternatingFaceMapComplex A).map (Functor.whiskerRight f (ModuleCat.free ℤ))
noncomputable def twoFreeMap (f:X⟶X') (g:Y⟶Y') : twoFree X Y ⟶ twoFree X' Y' :=
  (alternatingFaceMapComplex (ChainComplex A ℕ)).map
    (Functor.whiskerRight (Functor.curry.map
      (Functor.whiskerLeft (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse
        (Functor.whiskerRight (map f g) (ModuleCat.free ℤ)))) (alternatingFaceMapComplex A))
@[reassoc] lemma free_natural (f:X⟶X') (g:Y⟶Y') :
    EilenbergZilber.twoMap (map f g) ≫ (freeIso X' Y').hom =
      (freeIso X Y).hom ≫ twoFreeMap f g := by
  apply HomologicalComplex.Hom.ext; funext p
  apply HomologicalComplex.Hom.ext; funext q
  exact (FreeChains.naturalIso.hom.naturality ((map f g).app (op (SimplexCategory.mk p,SimplexCategory.mk q))))
noncomputable def tensorBiMap (f:X⟶X') (g:Y⟶Y') :
    TensorProductHomology.bicomplex (complex X) (complex Y) ⟶
      TensorProductHomology.bicomplex (complex X') (complex Y') :=
  (((curriedTensor A).mapBifunctorHomologicalComplex c c).map (chainMap f)).app (complex Y) ≫
    (((curriedTensor A).mapBifunctorHomologicalComplex c c).obj (complex X')).map (chainMap g)
@[reassoc] lemma tensor_natural (f:X⟶X') (g:Y⟶Y') :
    tensorBiMap f g ≫ (tensorIso X' Y').hom = (tensorIso X Y).hom ≫ twoFreeMap f g := by
  apply HomologicalComplex.Hom.ext; funext p
  apply HomologicalComplex.Hom.ext; funext q
  simp only [tensorBiMap,tensorIso,rowIso,twoFreeMap,HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  change (((ModuleCat.free ℤ).map (f.app (op ⦋p⦌))) ▷ ((ModuleCat.free ℤ).obj (Y.obj (op ⦋q⦌))) ≫
    ((ModuleCat.free ℤ).obj (X'.obj (op ⦋p⦌))) ◁ ((ModuleCat.free ℤ).map (g.app (op ⦋q⦌)))) ≫
      Functor.LaxMonoidal.μ (ModuleCat.free ℤ) _ _ =
    Functor.LaxMonoidal.μ (ModuleCat.free ℤ) _ _ ≫
      (ModuleCat.free ℤ).map (f.app (op ⦋p⦌) ⊗ₘ g.app (op ⦋q⦌))
  rw [←MonoidalCategory.tensorHom_def]
  exact Functor.LaxMonoidal.μ_natural (ModuleCat.free ℤ) _ _
noncomputable def homologyIsoN (X Y:SSet) (n:ℕ) :
    (X⊗Y).homology Z n ≅ ((complex X⊗complex Y).homology n) :=
  EilenbergZilber.homologyIsoN (product X Y) n ≪≫
      (homologyFunctor A c n).mapIso (total.mapIso (freeIso X Y ≪≫ (tensorIso X Y).symm) c)
@[reassoc] lemma homology_natural (f:X⟶X') (g:Y⟶Y') (n:ℕ) :
    SSet.homologyMap (f⊗ₘg) Z n ≫ (homologyIsoN X' Y' n).hom =
      (homologyIsoN X Y n).hom ≫ homologyMap (chainMap f⊗ₘchainMap g) n := by
  have ht : EilenbergZilber.twoMap (map f g) ≫
      (freeIso X' Y' ≪≫ (tensorIso X' Y').symm).hom =
    (freeIso X Y ≪≫ (tensorIso X Y).symm).hom ≫ tensorBiMap f g := by
    simp only [Iso.trans_hom,Iso.symm_hom]
    rw [←Category.assoc,free_natural,Category.assoc]
    apply (cancel_mono (tensorIso X' Y').hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [tensor_natural]
    simp
  have hh := EilenbergZilber.homology_natural (map f g) n
  have ht' := congrArg (fun φ => homologyMap (total.map φ c) n) ht
  simp only [total.map_comp,homologyMap_comp] at ht'
  simp only [homologyIsoN]

  change homologyMap (EilenbergZilber.diagonalMap (map f g)) n ≫
      (EilenbergZilber.homologyIsoN (product X' Y') n).hom ≫
        homologyMap (total.map (freeIso X' Y' ≪≫ (tensorIso X' Y').symm).hom c) n =
    (EilenbergZilber.homologyIsoN (product X Y) n).hom ≫
      homologyMap (total.map (freeIso X Y ≪≫ (tensorIso X Y).symm).hom c) n ≫
        homologyMap (total.map (tensorBiMap f g) c) n
  rw [reassoc_of% hh,ht']
end ProductChains

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R:Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

lemma flatPresentation (A:ModuleCat.{0} R) :
    ∃S:ShortComplex (ModuleCat.{0} R),S.X₃=A ∧ S.ShortExact ∧
      Module.Flat R S.X₁ ∧ Module.Flat R S.X₂ := by
  let φ : (A→₀R) →ₗ[R] A := Finsupp.linearCombination R (fun x:A => x)
  have hφ : Function.Surjective φ := by
    intro x; exact ⟨Finsupp.single x 1,by simp [φ]⟩
  let B : ModuleCat R := ModuleCat.of R (A→₀R)
  let C : ModuleCat R := ModuleCat.of R φ.ker
  let i : C ⟶ B := ModuleCat.ofHom φ.ker.subtype
  let p : B ⟶ A := ModuleCat.ofHom φ
  have hi : Mono i := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hp : Epi p := (ModuleCat.epi_iff_surjective _).mpr hφ
  have hz : i≫p=0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; exact x.property
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk i p hz
  have he : S.ShortExact := {
    mono_f := hi
    epi_g := hp
    exact := (S.moduleCat_exact_iff).mpr (by intro x hx; exact ⟨⟨x,hx⟩,rfl⟩) }
  exact ⟨S,rfl,he,inferInstance,inferInstance⟩
variable (K:ChainComplex (ModuleCat.{0} R) ℕ)
omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma flat_isZero (A:ModuleCat.{0} R) [Module.Flat R A] (n:ℕ)
    (h:IsZero (K.homology n)) : IsZero ((homologyFunctor K n).obj A) := by
  exact IsZero.of_iso (Functor.map_isZero (tensorRight A) h)
    ((K.sc n).mapHomologyIso (tensorRight A))
variable [∀n,Module.Flat R (K.X n)]
lemma arbitrary_zero_succ (A:ModuleCat.{0} R) (n:ℕ)
    (h0:IsZero (K.homology n)) (h1:IsZero (K.homology (n+1))) :
    IsZero ((homologyFunctor K (n+1)).obj A) := by
  obtain ⟨S,hA,hS,h1f,h2f⟩ := flatPresentation A
  have := h1f; have := h2f
  rw [←hA]
  exact ((shortExact K hS).homology_exact₃ (n+1) n rfl).isZero_X₂
    ((flat_isZero K S.X₂ (n+1) h1).eq_of_src _ _)
    ((flat_isZero K S.X₁ n h0).eq_of_tgt _ _)
lemma arbitrary_zero_zero (A:ModuleCat.{0} R) (h:IsZero (K.homology 0)) :
    IsZero ((homologyFunctor K 0).obj A) := by
  obtain ⟨S,hA,hS,h1f,h2f⟩ := flatPresentation A
  have := h1f; have := h2f
  rw [←hA]
  have hs := shortExact K hS
  have := hs.epi_g
  have homology_epi : Epi (homologyMap (S.map (functor K)).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro _; simp [ComplexShape.down_Rel])
  exact @IsZero.of_epi _ _ _ _ _ (homologyMap (S.map (functor K)).g 0)
    homology_epi (flat_isZero K S.X₂ 0 h)
end TensorCoefficient

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R:Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
lemma arbitrary_isZero (K L:ChainComplex (ModuleCat.{0} R) ℕ)
    [∀n,Module.Flat R (K.X n)] (a b n:ℕ) (hn:n<a+b)
    (hK:∀i,i<a→IsZero (K.homology i)) (hL:∀i,i<b→IsZero (L.homology i)) :
    IsZero (((bicomplex K L).total c).homology n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply TotalFiniteness.subsingleton
  intro p q hpq
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply IsZero.of_iso _ ((homologyFunctor _ c p).mapIso (rowIso K L q))
  by_cases hq:q<b
  · exact Functor.map_isZero (TensorCoefficient.homologyFunctor K p) (hL q hq)
  · cases p with
    | zero => exact TensorCoefficient.arbitrary_zero_zero K _ (hK 0 (by omega))
    | succ p => exact TensorCoefficient.arbitrary_zero_succ K _ p (hK p (by omega)) (hK (p+1) (by omega))
end TensorProductHomology
namespace ChainTensor
open FreeChains

instance monoidalPreadditive : MonoidalPreadditive (ChainComplex A ℕ) where
  whiskerLeft_zero := fun {K L M} => (tensorLeft K).map_zero L M
  zero_whiskerRight := fun {K L M} => (tensorRight K).map_zero L M
  whiskerLeft_add := fun {K _ _} f g => (tensorLeft K).map_add (f:=f) (g:=g)
  add_whiskerRight := fun {K _ _} f g => (tensorRight K).map_add (f:=f) (g:=g)
end ChainTensor

end

end

end OAI

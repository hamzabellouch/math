import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.AlternatingH2
import OAI.GroupTheory.SimpleAmenable.Homology.TotalFiniteness
import OAI.GroupTheory.SimpleAmenable.Homology.FreeChains

namespace OAI

section

section

open CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

lemma presentation (A : ModuleCat.{0} R) [Module.Finite R A] :
    ∃ S : ShortComplex (ModuleCat.{0} R), S.X₃=A ∧ S.ShortExact ∧
      Module.Finite R S.X₁ ∧ Module.Free R S.X₁ ∧ Module.Finite R S.X₂ ∧ Module.Free R S.X₂ := by
  obtain ⟨n,φ,hφ⟩ := Module.Finite.exists_fin' R A
  let B : ModuleCat R := ModuleCat.of R (Fin n → R)
  let C : ModuleCat R := ModuleCat.of R φ.ker
  let i : C ⟶ B := ModuleCat.ofHom φ.ker.subtype
  let p : B ⟶ A := ModuleCat.ofHom φ
  have hi : Mono i := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have hp : Epi p := (ModuleCat.epi_iff_surjective _).mpr hφ
  have hz : i≫p=0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact x.property
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk i p hz
  have he : S.ShortExact := {
    mono_f := hi
    epi_g := hp
    exact := (S.moduleCat_exact_iff).mpr (by
      intro x hx
      exact ⟨⟨x,hx⟩,rfl⟩) }
  have : Module.Finite R C := Module.Finite.of_injective φ.ker.subtype Subtype.val_injective
  have : Module.Free R C := Module.free_of_finite_type_torsion_free'
  exact ⟨S,rfl,he,inferInstance,inferInstance,inferInstance,inferInstance⟩

variable (K : ChainComplex (ModuleCat.{0} R) ℕ) [∀n,Module.Flat R (K.X n)]

lemma finite_coefficient_succ (A : ModuleCat.{0} R) [Module.Finite R A] (n : ℕ)
    [Module.Finite R (K.homology n)] [Module.Finite R (K.homology (n+1))] :
    Module.Finite R ((homologyFunctor K (n+1)).obj A) := by
  obtain ⟨S,hA,hS,h1,hf1,h2,hf2⟩ := presentation A
  have := h1; have := hf1; have := h2; have := hf2
  rw [←hA]
  have : Module.Finite R ((S.map (functor K)).X₁.homology n) := free_finite K S.X₁ n
  have : Module.Finite R ((S.map (functor K)).X₂.homology (n+1)) := free_finite K S.X₂ (n+1)
  exact FiniteHomologyReturn.finite_of_exact
    ((shortExact K hS).homology_exact₃ (n+1) n rfl)

lemma finite_coefficient_zero (A : ModuleCat.{0} R) [Module.Finite R A]
    [Module.Finite R (K.homology 0)] : Module.Finite R ((homologyFunctor K 0).obj A) := by
  obtain ⟨S,hA,hS,h1,hf1,h2,hf2⟩ := presentation A
  have := h1; have := hf1; have := h2; have := hf2
  rw [←hA]
  have : Module.Finite R ((S.map (functor K)).X₂.homology 0) := free_finite K S.X₂ 0
  have hs := shortExact K hS
  have := hs.epi_g
  have : Epi (homologyMap (S.map (functor K)).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro _; simp [ComplexShape.down_Rel])
  exact Module.Finite.of_surjective (homologyMap (S.map (functor K)).g 0).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma zero_coefficient_succ (A : ModuleCat.{0} R) [Module.Finite R A] (n : ℕ)
    (h0 : IsZero (K.homology n)) (h1 : IsZero (K.homology (n+1))) :
    IsZero ((homologyFunctor K (n+1)).obj A) := by
  obtain ⟨S,hA,hS,hf1,hfr1,hf2,hfr2⟩ := presentation A
  have := hf1; have := hfr1; have := hf2; have := hfr2
  rw [←hA]
  exact ((shortExact K hS).homology_exact₃ (n+1) n rfl).isZero_X₂
    ((free_isZero K S.X₂ (n+1) h1).eq_of_src _ _)
    ((free_isZero K S.X₁ n h0).eq_of_tgt _ _)

lemma zero_coefficient_zero (A : ModuleCat.{0} R) [Module.Finite R A]
    (h : IsZero (K.homology 0)) : IsZero ((homologyFunctor K 0).obj A) := by
  obtain ⟨S,hA,hS,h1,hf1,h2,hf2⟩ := presentation A
  have := h1; have := hf1; have := h2; have := hf2
  rw [←hA]
  have hs := shortExact K hS
  have := hs.epi_g
  have homology_epi : Epi (homologyMap (S.map (functor K)).g 0) :=
    epi_homologyMap_of_epi_of_not_rel _ 0 (by intro _; simp [ComplexShape.down_Rel])
  exact @IsZero.of_epi _ _ _ _ _ (homologyMap (S.map (functor K)).g 0)
    homology_epi (free_isZero K S.X₂ 0 h)

end TensorCoefficient

end

section

open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R : Type} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable (K L : ChainComplex (ModuleCat.{0} R) ℕ)
noncomputable def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) c c :=
  (((curriedTensor (ModuleCat.{0} R)).mapBifunctorHomologicalComplex c c).obj K).obj L

noncomputable def rowIso [∀n,Module.Flat R (K.X n)] (q : ℕ) :
    TotalFiniteness.row (bicomplex K L) q ≅ (TensorCoefficient.functor K).obj (L.homology q) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (L.sc q).mapHomologyIso (tensorLeft (K.X p))) ?_
  intro p p' _
  symm
  change ShortComplex.homologyMap ((L.sc q).mapNatTrans
      ((tensoringLeft (ModuleCat R)).map (K.d p p'))) ≫ _ = _
  apply (Iso.eq_comp_inv ((L.sc q).mapHomologyIso (tensorLeft (K.X p')))).mp
  exact (ShortComplex.homologyMap_mapNatTrans (L.sc q)
    ((tensoringLeft (ModuleCat R)).map (K.d p p'))).trans (Category.assoc _ _ _).symm

lemma finite [IsDomain R] [IsPrincipalIdealRing R] [∀n,Module.Flat R (K.X n)]
    (n : ℕ) (hK : ∀i,i≤n → Module.Finite R (K.homology i))
    (hL : ∀i,i≤n → Module.Finite R (L.homology i)) :
    Module.Finite R (((bicomplex K L).total c).homology n) := by
  apply TotalFiniteness.finite
  intro p q hpq
  have := hL q (by omega)
  have := hK p (by omega)
  have : Module.Finite R ((homologyFunctor (ModuleCat R) c p).obj ((TensorCoefficient.functor K).obj (L.homology q))) := by
    cases p with
    | zero => exact TensorCoefficient.finite_coefficient_zero K _
    | succ p =>
      have := hK p (by omega)
      exact TensorCoefficient.finite_coefficient_succ K _ p
  exact Module.Finite.equiv ((homologyFunctor _ c p).mapIso (rowIso K L q)).symm.toLinearEquiv

lemma isZero [IsDomain R] [IsPrincipalIdealRing R] [∀n,Module.Flat R (K.X n)]
    (a b n : ℕ) (hn : n<a+b)
    (hK : ∀i,i<a → IsZero (K.homology i))
    (hL : ∀i,i<b → IsZero (L.homology i))
    (hfL : ∀i,i≤n → Module.Finite R (L.homology i)) :
    IsZero (((bicomplex K L).total c).homology n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply TotalFiniteness.subsingleton
  intro p q hpq
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply IsZero.of_iso _ ((homologyFunctor _ c p).mapIso (rowIso K L q))
  by_cases hq : q<b
  · exact Functor.map_isZero (TensorCoefficient.homologyFunctor K p) (hL q hq)
  · have := hfL q (by omega)
    cases p with
    | zero => exact TensorCoefficient.zero_coefficient_zero K _ (hK 0 (by omega))
    | succ p => exact TensorCoefficient.zero_coefficient_succ K _ p (hK p (by omega)) (hK (p+1) (by omega))

end TensorProductHomology

end

end

end OAI

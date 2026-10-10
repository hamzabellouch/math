import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.FreeCech
import OAI.AlgebraicGeometry.RelativeTriviality.BaseChange
import OAI.AlgebraicGeometry.RelativeTriviality.AffineSquare
import OAI.AlgebraicGeometry.RelativeTriviality.LocallyFree
import OAI.AlgebraicGeometry.RelativeTriviality.LaurentCech

namespace OAI

noncomputable section

namespace CampanaPeternellSix.ActualCech
section
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange RelativePolynomialEvaluation
open Scheme.Modules
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma baseMap_scalars :
    CommRingCat.ofHom (RelativeLineGlobalFunctions.scalars R) ≫ (baseMap (algebraMap R S) 1).appTop =
      CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom (RelativeLineGlobalFunctions.scalars S) := by
  exact AffineSquare.baseScalars_natural (baseMap (algebraMap R S) 1) (toBase S 1) (toBase R 1)
    (CommRingCat.ofHom (algebraMap R S)) (baseMap_isPullback (algebraMap R S))

def actualUnit (E : (scheme R).Modules) (U : (scheme R).Opens) (V : (scheme S).Opens)
    (hV : V ≤ (baseMap (algebraMap R S) 1) ⁻¹ᵁ U) :
    let N := (coefficientSheaf S ((pullback (baseMap (algebraMap R S) 1)).obj E)).obj.obj (op V)
    letI : Module R N := Module.compHom N (algebraMap R S)
    ((coefficientSheaf R E).obj.obj (op U)) →ₗ[R] N := by
  let N := (coefficientSheaf S ((pullback (baseMap (algebraMap R S) 1)).obj E)).obj.obj (op V)
  letI : Module R N := Module.compHom N (algebraMap R S)
  let f := AffineSquare.coefficientUnit (baseMap (algebraMap R S) 1)
    (CommRingCat.ofHom (algebraMap R S))
    (@CommRingCat.ofHom R Γ(scheme R,⊤) inferInstance inferInstance (RelativeLineGlobalFunctions.scalars R))
    (@CommRingCat.ofHom S Γ(scheme S,⊤) inferInstance inferInstance (RelativeLineGlobalFunctions.scalars S)) baseMap_scalars E U V hV
  exact { toFun := f, map_add' := map_add f, map_smul' := f.map_smul' }

lemma actualUnit_isBaseChange (E : (scheme R).Modules) [E.IsQuasicoherent]
    (U : (scheme R).Opens) (V : (scheme S).Opens)
    (hUaff : IsAffineOpen U) (hVaff : IsAffineOpen V)
    (hUV : V = (baseMap (algebraMap R S) 1) ⁻¹ᵁ U) :
    let N := (coefficientSheaf S ((pullback (baseMap (algebraMap R S) 1)).obj E)).obj.obj (op V)
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange S (actualUnit E U V hUV.le) := by
  exact AffineSquare.coefficientUnit_isBaseChange_of_isPushout
    (X := scheme S) (Y := scheme R)
    (baseMap (algebraMap R S) 1)
    (@CommRingCat.ofHom R Γ(scheme R,⊤) inferInstance inferInstance (RelativeLineGlobalFunctions.scalars R))
    (@CommRingCat.ofHom S Γ(scheme S,⊤) inferInstance inferInstance (RelativeLineGlobalFunctions.scalars S)) baseMap_scalars U V hUV.le
    hUaff hVaff
    (AffineSquare.openBaseScalars_pushout (baseMap (algebraMap R S) 1) (toBase S 1) (toBase R 1)
      (CommRingCat.ofHom (algebraMap R S)) (baseMap_isPullback (algebraMap R S)) U V hUaff hVaff hUV) E

lemma actualUnit_naturality (E : (scheme R).Modules)
    (U₁ U₂ : (scheme R).Opens) (V₁ V₂ : (scheme S).Opens)
    (hU : U₁ ≤ U₂) (hV : V₁ ≤ V₂)
    (hv₁ : V₁ ≤ (baseMap (algebraMap R S) 1) ⁻¹ᵁ U₁)
    (hv₂ : V₂ ≤ (baseMap (algebraMap R S) 1) ⁻¹ᵁ U₂)
    (m : (coefficientSheaf R E).obj.obj (op U₂)) :
    actualUnit E U₁ V₁ hv₁ ((coefficientSheaf R E).obj.map (homOfLE hU).op m) =
    (coefficientSheaf S ((pullback (baseMap (algebraMap R S) 1)).obj E)).obj.map (homOfLE hV).op
      (actualUnit E U₂ V₂ hv₂ m) := by
  exact AffineSquare.coefficientUnit_naturality (baseMap (algebraMap R S) 1)
    (CommRingCat.ofHom (algebraMap R S))
    (@CommRingCat.ofHom R Γ(scheme R,⊤) inferInstance inferInstance (RelativeLineGlobalFunctions.scalars R))
    (@CommRingCat.ofHom S Γ(scheme S,⊤) inferInstance inferInstance (RelativeLineGlobalFunctions.scalars S)) baseMap_scalars E U₁ U₂ V₁ V₂ hU hV hv₁ hv₂ m
end

section
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts
universe u
variable (R : Type u) [CommRing R]

lemma iso_ranges_top {E F : (scheme R).Modules} (e : E ≅ F)
    (hF : leftImage R F ⊔ rightImage R F = ⊤) :
    leftImage R E ⊔ rightImage R E = ⊤ := by
  apply top_unique
  intro m hm
  change Γ(E,leftOpen R ⊓ rightOpen R) at m
  let mf : overlapModule R F := e.hom.app (leftOpen R ⊓ rightOpen R) m
  have h : mf ∈ leftImage R F ⊔ rightImage R F := by
    rw [hF]
    trivial
  obtain ⟨a,⟨x,hx⟩,b,⟨y,hy⟩,hab⟩ := Submodule.mem_sup.mp h
  subst a
  subst b
  let x' := e.inv.app (leftOpen R) x
  let y' := e.inv.app (rightOpen R) y
  have hx' : e.inv.app (leftOpen R ⊓ rightOpen R)
      (F.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op x) =
      E.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op x' :=
    ConcreteCategory.congr_hom (e.inv.val.naturality (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op) x
  have hy' : e.inv.app (leftOpen R ⊓ rightOpen R)
      (F.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op y) =
      E.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op y' :=
    ConcreteCategory.congr_hom (e.inv.val.naturality (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op) y
  have he : e.inv.app (leftOpen R ⊓ rightOpen R) (e.hom.app (leftOpen R ⊓ rightOpen R) m) = m := by
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.app (leftOpen R ⊓ rightOpen R)) e.hom_inv_id) m
  refine Submodule.mem_sup.mpr ⟨_,⟨x',rfl⟩,_,⟨y',rfl⟩,?_⟩
  have hs := congrArg (fun z => e.inv.app (leftOpen R ⊓ rightOpen R) z) hab
  change _ + _ = m
  change e.inv.app (leftOpen R ⊓ rightOpen R)
    (F.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op x +
     F.presheaf.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op y) =
    e.inv.app (leftOpen R ⊓ rightOpen R) (e.hom.app (leftOpen R ⊓ rightOpen R) m) at hs
  rw [map_add,hx',hy',he] at hs
  exact hs

lemma trivial_ranges_top (E : (scheme R).Modules) (n : ℕ)
    (hf : Nonempty (E ≅ SheafOfModules.free (ULift.{u} (Fin n)))) :
    leftImage R E ⊔ rightImage R E = ⊤ := by
  obtain ⟨e⟩ := hf
  exact iso_ranges_top R e (free_ranges_top (ULift.{u} (Fin n)) R)
end

section
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange
open Scheme.Modules
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R]

lemma left_affine : IsAffineOpen (leftOpen R) :=
  Proj.isAffineOpen_basicOpen (grading R) (x₀ R) (x₀_mem R) (by decide : 0 < 1)
lemma right_affine : IsAffineOpen (rightOpen R) :=
  Proj.isAffineOpen_basicOpen (grading R) (x₁ R) (x₁_mem R) (by decide : 0 < 1)
lemma overlap_affine : IsAffineOpen (leftOpen R ⊓ rightOpen R) := by
  rw [overlap_eq_basic]
  exact Proj.isAffineOpen_basicOpen (grading R) (x₀ R * x₁ R)
    (SetLike.mul_mem_graded (x₀_mem R) (x₁_mem R)) (by decide : 0 < 1+1)

variable {R} {S : Type u} [CommRing S] [Algebra R S]
lemma left_base_preimage : leftOpen S = (baseMap (algebraMap R S) 1) ⁻¹ᵁ leftOpen R := by
  dsimp only [leftOpen, baseMap, x₀]
  erw [Proj.map_preimage_basicOpen, coefficientMap_X]
lemma right_base_preimage : rightOpen S = (baseMap (algebraMap R S) 1) ⁻¹ᵁ rightOpen R := by
  dsimp only [rightOpen, baseMap, x₁]
  erw [Proj.map_preimage_basicOpen, coefficientMap_X]
lemma overlap_base_preimage : leftOpen S ⊓ rightOpen S =
    (baseMap (algebraMap R S) 1) ⁻¹ᵁ (leftOpen R ⊓ rightOpen R) := by
  erw [Scheme.Hom.preimage_inf]
  rw [← left_base_preimage, ← right_base_preimage]
  rfl

lemma tensor_actual_cech_vanish_of_trivial_pullback (E : (scheme R).Modules) [E.IsQuasicoherent]
    (n : ℕ) (hf : Nonempty ((pullback (baseMap (algebraMap R S) 1)).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin n)))) :
    Subsingleton (S ⊗[R] quotient R E) := by
  let E' := (pullback (baseMap (algebraMap R S) 1)).obj E
  let P := (coefficientSheaf R E).obj.obj (op (leftOpen R))
  let Q := (coefficientSheaf R E).obj.obj (op (rightOpen R))
  let M := overlapModule R E
  let P' := (coefficientSheaf S E').obj.obj (op (leftOpen S))
  let Q' := (coefficientSheaf S E').obj.obj (op (rightOpen S))
  let M' := overlapModule S E'
  let : Module R P' := Module.compHom P' (algebraMap R S)
  let : Module R Q' := Module.compHom Q' (algebraMap R S)
  let : Module R M' := Module.compHom M' (algebraMap R S)
  let : IsScalarTower R S P' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R S Q' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R S M' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let a : P →ₗ[R] M := ((coefficientSheaf R E).obj.map (homOfLE inf_le_left).op).hom
  let b : Q →ₗ[R] M := ((coefficientSheaf R E).obj.map (homOfLE inf_le_right).op).hom
  let a' : P' →ₗ[S] M' := ((coefficientSheaf S E').obj.map (homOfLE inf_le_left).op).hom
  let b' : Q' →ₗ[S] M' := ((coefficientSheaf S E').obj.map (homOfLE inf_le_right).op).hom
  let p : P →ₗ[R] P' := actualUnit E _ _ left_base_preimage.le
  let q : Q →ₗ[R] Q' := actualUnit E _ _ right_base_preimage.le
  let m : M →ₗ[R] M' := actualUnit E _ _ overlap_base_preimage.le
  have hp : IsBaseChange S p := actualUnit_isBaseChange E _ _ (left_affine R) (left_affine S) left_base_preimage
  have hq : IsBaseChange S q := actualUnit_isBaseChange E _ _ (right_affine R) (right_affine S) right_base_preimage
  have hm : IsBaseChange S m := actualUnit_isBaseChange E _ _ (overlap_affine R) (overlap_affine S) overlap_base_preimage
  exact RelativeCech.tensor_cech_vanish R S P Q M P' Q' M' a b a' b' p q m hp hq hm
    (fun x => actualUnit_naturality E _ _ _ _ inf_le_left inf_le_left _ _ x)
    (fun x => actualUnit_naturality E _ _ _ _ inf_le_right inf_le_right _ _ x)
    (trivial_ranges_top S E' n hf)
end

open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange
universe u
variable (R : Type u) [CommRing R] (E : (scheme R).Modules)
abbrev globalModule : ModuleCat R := (coefficientSheaf R E).obj.obj (op ⊤)
abbrev pairModule := ((coefficientSheaf R E).obj.obj (op (leftOpen R))) ×
  ((coefficientSheaf R E).obj.obj (op (rightOpen R)))
def sectionPair : globalModule R E →ₗ[R] pairModule R E :=
  ((coefficientSheaf R E).obj.map (homOfLE (show leftOpen R ≤ ⊤ from le_top)).op).hom.prod
    ((coefficientSheaf R E).obj.map (homOfLE (show rightOpen R ≤ ⊤ from le_top)).op).hom
def difference : pairModule R E →ₗ[R] overlapModule R E :=
  ((coefficientSheaf R E).obj.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op).hom.comp (LinearMap.fst R _ _) -
    ((coefficientSheaf R E).obj.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op).hom.comp (LinearMap.snd R _ _)
lemma sectionPair_injective : Function.Injective (sectionPair R E) := by
  intro x y h
  exact (coefficientSheaf R E).eq_of_locally_eq₂
    (homOfLE le_top : leftOpen R ⟶ ⊤) (homOfLE le_top : rightOpen R ⟶ ⊤)
    (by rw [standard_cover R]) x y (congrArg Prod.fst h) (congrArg Prod.snd h)
lemma difference_sectionPair : (difference R E).comp (sectionPair R E) = 0 := by
  ext s
  change (coefficientSheaf R E).obj.map _ ((coefficientSheaf R E).obj.map _ s) -
    (coefficientSheaf R E).obj.map _ ((coefficientSheaf R E).obj.map _ s) = 0
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  exact sub_self _
lemma sectionPair_exact : Function.Exact (sectionPair R E) (difference R E) := by
  intro x
  constructor
  · intro hx
    have hab : (coefficientSheaf R E).obj.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ leftOpen R from inf_le_left)).op x.1 =
      (coefficientSheaf R E).obj.map (homOfLE (show leftOpen R ⊓ rightOpen R ≤ rightOpen R from inf_le_right)).op x.2 :=
      sub_eq_zero.mp hx
    let U : Bool → (scheme R).Opens := fun i => if i then leftOpen R else rightOpen R
    let sf : ∀ i, (coefficientSheaf R E).obj.obj (op (U i)) := fun i =>
      if h : i then by simpa [U,h] using x.1 else by simpa [U,h] using x.2
    have hc : TopCat.Presheaf.IsCompatible (coefficientSheaf R E).obj U sf := by
      intro i j
      cases i <;> cases j
      · rfl
      · have he := congrArg ((coefficientSheaf R E).obj.map (eqToHom (inf_comm (rightOpen R) (leftOpen R))).op) hab
        simpa [U,sf, TopologicalSpace.Opens.infLELeft, TopologicalSpace.Opens.infLERight,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp] using he.symm
      · exact hab
      · rfl
    obtain ⟨s,hs,_⟩ := (coefficientSheaf R E).existsUnique_gluing' U ⊤
      (fun _ => homOfLE le_top) (by
        rw [← standard_cover R]
        exact sup_le (le_iSup U true) (le_iSup U false)) sf hc
    refine ⟨s,?_⟩
    exact Prod.ext (hs true) (hs false)
  · rintro ⟨s,rfl⟩
    exact LinearMap.congr_fun (difference_sectionPair R E) s
end CampanaPeternellSix.ActualCech

namespace CampanaPeternellSix.RelativeCech
section
open scoped TensorProduct
open TensorProduct
universe u
variable {R : Type u} [CommRing R]
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
lemma left_exact_residue_baseChange (p : PrimeSpectrum R)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hex : Function.Exact f g) (hinj : Function.Injective f)
    [Module.Flat R M₃] [Module.Finite R (M₃ ⧸ LinearMap.range g)]
    [Subsingleton (p.asIdeal.ResidueField ⊗[R] (M₃ ⧸ LinearMap.range g))] :
    Function.Exact (f.baseChange p.asIdeal.ResidueField) (g.baseChange p.asIdeal.ResidueField) ∧
      Function.Injective (f.baseChange p.asIdeal.ResidueField) := by
  let Q := M₃ ⧸ LinearMap.range g
  let Rp := Localization.AtPrime p.asIdeal
  let K := p.asIdeal.ResidueField
  have hnot : p ∉ Module.support R Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial _
  let : Subsingleton (LocalizedModule p.asIdeal.primeCompl Q) := Module.notMem_support_iff.mp hnot
  let : Subsingleton (Rp ⊗[R] Q) :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl Q).symm.injective.subsingleton
  have hQ : Function.Exact g (LinearMap.range g).mkQ := by
    intro x
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    rfl
  have hsurj : Function.Surjective (g.baseChange Rp) := by
    have h := lTensor_exact Rp hQ (LinearMap.range g).mkQ_surjective
    intro x
    exact (h x).mp (Subsingleton.elim _ _)
  have hRp : Function.Exact (f.baseChange Rp) (g.baseChange Rp) :=
    Module.Flat.lTensor_exact Rp hex
  have hinjRp : Function.Injective (f.baseChange Rp) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hinj
  have hKK : Function.Exact ((f.baseChange Rp).baseChange K) ((g.baseChange Rp).baseChange K) :=
    lTensor_exact K hRp hsurj
  have hinjKK : Function.Injective ((f.baseChange Rp).baseChange K) :=
    LinearMap.lTensor_injective_of_exact_of_flat (g.baseChange Rp) hsurj
      (f.baseChange Rp) hinjRp hRp K
  let e₁ := AlgebraTensorModule.cancelBaseChange R Rp K K M₁
  let e₂ := AlgebraTensorModule.cancelBaseChange R Rp K K M₂
  let e₃ := AlgebraTensorModule.cancelBaseChange R Rp K K M₃
  have hc₁ : (f.baseChange K).comp e₁.toLinearMap =
      e₂.toLinearMap.comp ((f.baseChange Rp).baseChange K) := by
    exact AlgebraTensorModule.lTensor_comp_cancelBaseChange R Rp K f
  have hc₂ : (g.baseChange K).comp e₂.toLinearMap =
      e₃.toLinearMap.comp ((g.baseChange Rp).baseChange K) := by
    exact AlgebraTensorModule.lTensor_comp_cancelBaseChange R Rp K g
  refine ⟨Function.Exact.of_ladder_linearEquiv_of_exact hc₁ hc₂ hKK, ?_⟩
  intro x y hxy
  apply e₁.symm.injective
  apply hinjKK
  apply e₂.injective
  have hx := congrArg (fun l : (K ⊗[Rp] (Rp ⊗[R] M₁)) →ₗ[K] (K ⊗[R] M₂) => l (e₁.symm x)) hc₁
  have hy := congrArg (fun l : (K ⊗[Rp] (Rp ⊗[R] M₁)) →ₗ[K] (K ⊗[R] M₂) => l (e₁.symm y)) hc₁
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hx hy
  exact hx.symm.trans (hxy.trans hy)
end

open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (p : PrimeSpectrum R)
variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type u} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module (p.asIdeal.ResidueField) N₁] [Module (p.asIdeal.ResidueField) N₂] [Module (p.asIdeal.ResidueField) N₃]
  [IsScalarTower R (p.asIdeal.ResidueField) N₁] [IsScalarTower R (p.asIdeal.ResidueField) N₂] [IsScalarTower R (p.asIdeal.ResidueField) N₃]
  (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃)
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[(p.asIdeal.ResidueField)] N₂} {g' : N₂ →ₗ[(p.asIdeal.ResidueField)] N₃}
lemma isBaseChange_of_left_exact_at_prime
    (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂) [Module.Flat R M₃]
    [Module.Finite R (M₃ ⧸ LinearMap.range g)]
    [Subsingleton ((p.asIdeal.ResidueField) ⊗[R] (M₃ ⧸ LinearMap.range g))]
    (isb₂ : IsBaseChange (p.asIdeal.ResidueField) h₂) (isb₃ : IsBaseChange (p.asIdeal.ResidueField) h₃)
    (exact₁ : Function.Exact f g) (inj₁ : Function.Injective f)
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange (p.asIdeal.ResidueField) h₁ := by
  simp only [IsBaseChange, IsTensorProduct] at isb₂ isb₃ ⊢
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((f.baseChange (p.asIdeal.ResidueField)).restrictScalars R) ((g.baseChange (p.asIdeal.ResidueField)).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exact₂ isb₂ isb₃.1 ?_ inj₂
  · ext s m
    simpa using congr(s • ($comm₁ m)).symm
  · ext s m
    simpa using congr(s • ($comm₂ m)).symm
  · exact (left_exact_residue_baseChange p f g exact₁ inj₁).1
  · exact (left_exact_residue_baseChange p f g exact₁ inj₁).2
end CampanaPeternellSix.RelativeCech

namespace CampanaPeternellSix.ActualCech
section
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange Scheme.Modules
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (x : PrimeSpectrum R)
lemma global_sections_base_change_prime_core (E : (scheme R).Modules) [E.IsQuasicoherent]
    [Module.Flat R (overlapModule R E)]
    [Module.Finite R ((overlapModule R E) ⧸ LinearMap.range (difference R E))]
    [Subsingleton ((x.asIdeal.ResidueField) ⊗[R] ((overlapModule R E) ⧸ LinearMap.range (difference R E)))] :
    let N := (coefficientSheaf (x.asIdeal.ResidueField) ((pullback (baseMap (algebraMap R (x.asIdeal.ResidueField)) 1)).obj E)).obj.obj (op ⊤)
    letI : Module R N := Module.compHom N (algebraMap R (x.asIdeal.ResidueField))
    letI : IsScalarTower R (x.asIdeal.ResidueField) N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange (x.asIdeal.ResidueField) (actualUnit (S := x.asIdeal.ResidueField) E ⊤ ⊤ (by intro z _; trivial)) := by
  let E' := (pullback (baseMap (algebraMap R (x.asIdeal.ResidueField)) 1)).obj E
  let P' := (coefficientSheaf (x.asIdeal.ResidueField) E').obj.obj (op (leftOpen (x.asIdeal.ResidueField)))
  let Q' := (coefficientSheaf (x.asIdeal.ResidueField) E').obj.obj (op (rightOpen (x.asIdeal.ResidueField)))
  let M' := overlapModule (x.asIdeal.ResidueField) E'
  let N := globalModule (x.asIdeal.ResidueField) E'
  let : Module R P' := Module.compHom P' (algebraMap R (x.asIdeal.ResidueField))
  let : Module R Q' := Module.compHom Q' (algebraMap R (x.asIdeal.ResidueField))
  let : Module R M' := Module.compHom M' (algebraMap R (x.asIdeal.ResidueField))
  let : Module R N := Module.compHom N (algebraMap R (x.asIdeal.ResidueField))
  let : IsScalarTower R (x.asIdeal.ResidueField) P' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R (x.asIdeal.ResidueField) Q' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R (x.asIdeal.ResidueField) M' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R (x.asIdeal.ResidueField) N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let p : _ →ₗ[R] P' := actualUnit E _ _ left_base_preimage.le
  let q : _ →ₗ[R] Q' := actualUnit E _ _ right_base_preimage.le
  let m : overlapModule R E →ₗ[R] M' := actualUnit E _ _ overlap_base_preimage.le
  let g : globalModule R E →ₗ[R] N := actualUnit E ⊤ ⊤ (by intro z _; trivial)
  let pq : pairModule R E →ₗ[R] P' × Q' := p.prodMap q
  have hp : IsBaseChange (x.asIdeal.ResidueField) p := actualUnit_isBaseChange E _ _ (left_affine R) (left_affine (x.asIdeal.ResidueField)) left_base_preimage
  have hq : IsBaseChange (x.asIdeal.ResidueField) q := actualUnit_isBaseChange E _ _ (right_affine R) (right_affine (x.asIdeal.ResidueField)) right_base_preimage
  have hm : IsBaseChange (x.asIdeal.ResidueField) m := actualUnit_isBaseChange E _ _ (overlap_affine R) (overlap_affine (x.asIdeal.ResidueField)) overlap_base_preimage
  have hpq : IsBaseChange (x.asIdeal.ResidueField) pq := IsBaseChange.prodMap p q hp hq
  have hsec : pq.comp (sectionPair R E) = ((sectionPair (x.asIdeal.ResidueField) E').restrictScalars R).comp g := by
    apply LinearMap.ext
    intro s
    apply Prod.ext
    · exact actualUnit_naturality E (leftOpen R) ⊤ (leftOpen (x.asIdeal.ResidueField)) ⊤ le_top le_top _ _ s
    · exact actualUnit_naturality E (rightOpen R) ⊤ (rightOpen (x.asIdeal.ResidueField)) ⊤ le_top le_top _ _ s
  have hdiff : m.comp (difference R E) = ((difference (x.asIdeal.ResidueField) E').restrictScalars R).comp pq := by
    apply LinearMap.ext
    intro x
    change m (_ - _) = _ - _
    rw [map_sub]
    exact congrArg₂ (· - ·)
      (actualUnit_naturality E _ _ _ _ inf_le_left inf_le_left _ _ x.1)
      (actualUnit_naturality E _ _ _ _ inf_le_right inf_le_right _ _ x.2)
  exact RelativeCech.isBaseChange_of_left_exact_at_prime x g pq m hsec hdiff hpq hm
    (sectionPair_exact R E) (sectionPair_injective R E)
    (sectionPair_exact (x.asIdeal.ResidueField) E') (sectionPair_injective (x.asIdeal.ResidueField) E')
end

section
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange
universe u
variable (R : Type u) [CommRing R] (E : (scheme R).Modules)
lemma difference_range : LinearMap.range (difference R E) = leftImage R E ⊔ rightImage R E := by
  apply le_antisymm
  · rintro _ ⟨⟨x,y⟩,rfl⟩
    apply Submodule.sub_mem
    · exact Submodule.mem_sup_left ⟨x,rfl⟩
    · exact Submodule.mem_sup_right ⟨y,rfl⟩
  · intro m hm
    obtain ⟨a,⟨x,rfl⟩,b,⟨y,rfl⟩,hab⟩ := Submodule.mem_sup.mp hm
    refine ⟨(x,-y),?_⟩
    change _ - ((coefficientSheaf R E).obj.map _).hom (-y) = m
    rw [map_neg, sub_neg_eq_add]
    exact hab
end

section
open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange
open scoped Polynomial LaurentPolynomial
universe u
variable (R : Type u) [CommRing R]
lemma flat_overlap_base (E : (scheme R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.Flat R (overlapModule R E) := by
  let A := Γ(scheme R,leftOpen R ⊓ rightOpen R)
  let r : R →+* A := ((scheme R).presheaf.map (homOfLE
    (show leftOpen R ⊓ rightOpen R ≤ ⊤ from le_top)).op).hom.comp
      (RelativeLineGlobalFunctions.scalars R)
  let : Algebra R A := r.toAlgebra
  let e : A ≃ₗ[R] R[T;T⁻¹] := { overlapSectionEquiv R with
    map_smul' := fun a b => by
      change overlapSectionEquiv R (a • b) = a • overlapSectionEquiv R b
      rw [Algebra.smul_def, Algebra.smul_def]
      change overlapSectionEquiv R (r a * b) = LaurentPolynomial.C a * overlapSectionEquiv R b
      rw [map_mul]
      exact congrArg (· * overlapSectionEquiv R b) (scalar_overlap R a) }
  have : Module.Flat R A := Module.Flat.of_linearEquiv e
  have : Module.Flat A (overlapModule R E) :=
    RelativeCech.flat_affine_open (scheme R) E hE _ (overlap_affine R)
  let : IsScalarTower R A (overlapModule R E) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Flat.trans R A (overlapModule R E)

lemma difference_surjective_of_cech_zero (E : (scheme R).Modules)
    [Subsingleton (quotient R E)] : Function.Surjective (difference R E) := by
  have ht : leftImage R E ⊔ rightImage R E = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp inferInstance
  intro m
  have hm : m ∈ leftImage R E ⊔ rightImage R E := by rw [ht]; trivial
  obtain ⟨a,⟨x,rfl⟩,b,⟨y,rfl⟩,hab⟩ := Submodule.mem_sup.mp hm
  refine ⟨(x,-y),?_⟩
  change _ - ((coefficientSheaf R E).obj.map _).hom (-y) = m
  rw [map_neg, sub_neg_eq_add]
  exact hab
end

open CategoryTheory AlgebraicGeometry Opposite
open RelativeLineCharts RelativeProjectiveBaseChange Scheme.Modules
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]
theorem global_sections_base_change_at_trivial_fiber (E : (scheme R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (p : PrimeSpectrum R) (n : ℕ)
    (hf : Nonempty ((pullback (baseMap (algebraMap R p.asIdeal.ResidueField) 1)).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin n)))) :
    let S := p.asIdeal.ResidueField
    let N := (coefficientSheaf S ((pullback (baseMap (algebraMap R S) 1)).obj E)).obj.obj (op ⊤)
    letI : Module R N := Module.compHom N (algebraMap R S)
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange S (actualUnit (S := S) E ⊤ ⊤ (by intro z _; trivial)) := by
  have hfin := finite_actual_cech R E hE
  have hflat := flat_overlap_base R E hE
  obtain ⟨q,hq,ht⟩ := hE
  let := hq
  let := ht
  let : E.IsLocallyFree := q.isLocallyFree
  let : E.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  have hzero := tensor_actual_cech_vanish_of_trivial_pullback E n hf
  let : Module.Flat R (overlapModule R E) := hflat
  let : Module.Finite R ((overlapModule R E) ⧸ LinearMap.range (difference R E)) := by
    rw [difference_range]
    exact hfin
  let : Subsingleton (p.asIdeal.ResidueField ⊗[R]
      ((overlapModule R E) ⧸ LinearMap.range (difference R E))) := by
    rw [difference_range]
    exact hzero
  exact global_sections_base_change_prime_core p E
end CampanaPeternellSix.ActualCech

end

end OAI

import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CurveCech

namespace OAI


                                     
section

namespace MaximalSeshadri.ExtCokernel
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def higherQuotientEquiv (hS : S.ShortExact) (M : C) (n : ℕ)
    (hvan : ∀ x : Ext S.X₂ M (n+1), x = 0) :
    (Ext S.X₁ M n ⧸ LinearMap.range
      ((Ext.mk₀ S.f).precompOfLinear K M (zero_add n))) ≃ₗ[K]
      Ext S.X₃ M (n+1) := by
  let d := hS.extClass.precompOfLinear K M (show 1+n=n+1 by omega)
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _)
      (n₀ := n) (by omega)
    exact ⟨y,hy⟩
  have hk : LinearMap.range ((Ext.mk₀ S.f).precompOfLinear K M (zero_add n)) =
      d.ker := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact hS.extClass_comp_assoc (h := by omega) y
    · intro hx
      exact Ext.contravariant_sequence_exact₁ hS M x (by omega) hx
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)
end
end MaximalSeshadri.ExtCokernel

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpenMap_comp {U V W : Opens X} (h : U ⟶ V) (g : V ⟶ W) :
    freeOpenMap R h ≫ freeOpenMap R g = freeOpenMap R (h ≫ g) := by
  exact ((freeOpenFunctor R).map_comp h g).symm

def shortComplexMap {U V U' V' : Opens X} (hU : U ≤ U') (hV : V ≤ V') :
    shortComplex R U V ⟶ shortComplex R U' V' where
  τ₁ := freeOpenMap R (homOfLE (inf_le_inf hU hV))
  τ₂ := biprod.map (freeOpenMap R (homOfLE hU)) (freeOpenMap R (homOfLE hV))
  τ₃ := freeOpenMap R (homOfLE (sup_le_sup hU hV))
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [shortComplex, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
        biprod.lift_fst, freeOpenMap_comp]
      rfl
    · simp only [shortComplex, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
        biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg, freeOpenMap_comp]
      rfl
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [shortComplex, biprod.inl_map_assoc, biprod.inl_desc_assoc,
        biprod.inl_desc, freeOpenMap_comp]
      rfl
    · simp only [shortComplex, biprod.inr_map_assoc, biprod.inr_desc_assoc,
        biprod.inr_desc, freeOpenMap_comp]
      rfl
end
end MaximalSeshadri.ModuleMayerVietoris

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance surfaceCechLinear : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) :=
  sheafLinear X
local instance surfaceCechHasExt : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

local instance surfaceCechFreeHomGroup (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance surfaceCechFreeHomModule (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _

def openBoundary (M : X.Modules) (U V : X.Opens) (n : ℕ) :
    Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U ⊓ V)) M n →ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U ⊔ V)) M (n+1) :=
  (shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V).extClass.precompOfLinear Γ(X,⊤) M
    (by omega)

lemma openBoundary_left (M : X.Modules) (U V : X.Opens) (n : ℕ)
    (x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule U) M n) :
    openBoundary M U V n
      ((Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_left))).comp x
        (zero_add n)) = 0 := by
  let complex : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U V
  let exactness : complex.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V
  let projection : complex.X₂ ⟶ FiniteCoverCohomology.freeOpenModule U :=
    biprod.fst (X := FiniteCoverCohomology.freeOpenModule U)
      (Y := FiniteCoverCohomology.freeOpenModule V)
  let inclusion : complex.X₁ ⟶
      FiniteCoverCohomology.freeOpenModule U :=
    freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_left)
  have factor : complex.f ≫ projection = inclusion := by
    exact biprod.lift_fst (C := X.Modules)
      (X := FiniteCoverCohomology.freeOpenModule U)
      (Y := FiniteCoverCohomology.freeOpenModule V) _ _
  have boundaryZero := exactness.extClass_comp_assoc (C := X.Modules)
    (h := show 1 + n = n + 1 by omega)
    ((Ext.mk₀ (C := X.Modules) projection).comp x (zero_add n))
  rw [Ext.mk₀_comp_mk₀_assoc (C := X.Modules), factor] at boundaryZero
  exact boundaryZero

lemma openBoundary_right (M : X.Modules) (U V : X.Opens) (n : ℕ)
    (x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule V) M n) :
    openBoundary M U V n
      ((Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_right))).comp x
        (zero_add n)) = 0 := by
  let complex : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U V
  let exactness : complex.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V
  let projection : complex.X₂ ⟶ FiniteCoverCohomology.freeOpenModule V :=
    -(biprod.snd (X := FiniteCoverCohomology.freeOpenModule U)
      (Y := FiniteCoverCohomology.freeOpenModule V))
  let inclusion : complex.X₁ ⟶
      FiniteCoverCohomology.freeOpenModule V :=
    freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE inf_le_right)
  have factor : complex.f ≫ projection = inclusion := by
    exact (Preadditive.comp_neg _ _).trans
      ((congrArg Neg.neg (biprod.lift_snd (C := X.Modules)
        (X := FiniteCoverCohomology.freeOpenModule U)
        (Y := FiniteCoverCohomology.freeOpenModule V) _ _)).trans (neg_neg _))
  have boundaryZero := exactness.extClass_comp_assoc (C := X.Modules)
    (h := show 1 + n = n + 1 by omega)
    ((Ext.mk₀ (C := X.Modules) projection).comp x (zero_add n))
  rw [Ext.mk₀_comp_mk₀_assoc (C := X.Modules), factor] at boundaryZero
  exact boundaryZero

lemma openBoundary_natural (M : X.Modules) {U V U' V' : X.Opens}
    (hU : U ≤ U') (hV : V ≤ V') (n : ℕ)
    (x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U' ⊓ V')) M n) :
    openBoundary M U V n
      ((Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE (inf_le_inf hU hV)))).comp x
        (zero_add n)) =
      (Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE (sup_le_sup hU hV)))).comp
        (openBoundary M U' V' n x) (zero_add (n+1)) := by
  let complex : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U V
  let complex' : ShortComplex X.Modules := shortComplex (X := X.carrier) X.ringCatSheaf U' V'
  let exactness : complex.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V
  let exactness' : complex'.ShortExact := shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U' V'
  let morphism : complex ⟶ complex' := shortComplexMap (X := X.carrier) X.ringCatSheaf hU hV
  let extension : Ext.{1} (C := X.Modules) complex'.X₁ M n := x
  have naturality := exactness.extClass_naturality exactness' morphism
  change exactness.extClass.comp ((Ext.mk₀ (C := X.Modules) morphism.τ₁).comp extension (zero_add n))
      (show 1 + n = n + 1 by omega) =
    (Ext.mk₀ (C := X.Modules) morphism.τ₃).comp
      (exactness'.extClass.comp extension (show 1 + n = n + 1 by omega)) (zero_add (n+1))
  rw [← Ext.comp_assoc_of_second_deg_zero, naturality]
  exact Ext.comp_assoc _ _ _ (by omega) (by omega) (by omega)

def tripleOpen (U V W : X.Opens) : X.Opens := (U ⊓ W) ⊓ (V ⊓ W)

def overlapIso (U V W : X.Opens) :
    FiniteCoverCohomology.freeOpenModule ((U ⊓ W) ⊔ (V ⊓ W)) ≅
      FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊓ W) :=
  (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).mapIso (eqToIso (show ((U ⊓ W) ⊔ (V ⊓ W)) = ((U ⊔ V) ⊓ W) from
    (inf_sup_right U V W).symm))

def tripleSectionBoundary (M : X.Modules) (U V W : X.Opens) :
    OpenSections M (tripleOpen U V W) →ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W)) M 2 :=
  (openBoundary M (U ⊔ V) W 1).comp
    ((extSourceIso (overlapIso U V W) M 1).toLinearMap.comp
      ((openBoundary M (U ⊓ W) (V ⊓ W) 0).comp
        ((Ext.linearEquiv₀ (C := X.Modules) (R := Γ(X,⊤))
          (X := FiniteCoverCohomology.freeOpenModule (tripleOpen U V W)) (Y := M)).symm.toLinearMap.comp
          (freeOpenLinearEquiv M (tripleOpen U V W)).symm.toLinearMap)))

lemma openBoundary_surjective (M : X.Modules) (U V : X.Opens) (n : ℕ)
    (hU : ∀ x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule U) M (n+1), x = 0)
    (hV : ∀ x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule V) M (n+1), x = 0) :
    Function.Surjective (openBoundary M U V n) := by
  have hmid (y : Ext.{1} (C := X.Modules)
      (FiniteCoverCohomology.freeOpenModule U ⊞ FiniteCoverCohomology.freeOpenModule V)
      M (n+1)) : y = 0 := by
    apply (Ext.biprodAddEquiv (C := X.Modules)).injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  intro x
  exact Ext.contravariant_sequence_exact₃
    (shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V) M x (hmid _) (n₀ := n) (by omega)

theorem tripleSectionBoundary_surjective [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (hUW : IsAffineOpen (U ⊓ W)) (hVW : IsAffineOpen (V ⊓ W)) :
    Function.Surjective (tripleSectionBoundary M U V W) := by
  apply Function.Surjective.comp
    (openBoundary_surjective M (U ⊔ V) W 1
        (ModuleMayerVietoris.union_ext_zero (X := X.carrier) X.ringCatSheaf U V M 1
        (FiniteCoverCohomology.affine_open_ext_zero U hU M 1)
        (FiniteCoverCohomology.affine_open_ext_zero V hV M 1)
        (FiniteCoverCohomology.affine_open_ext_zero (U ⊓ V) hUV M 0))
      (FiniteCoverCohomology.affine_open_ext_zero W hW M 1))
  apply Function.Surjective.comp (extSourceIso (overlapIso U V W) M 1).surjective
  apply Function.Surjective.comp
    (openBoundary_surjective M (U ⊓ W) (V ⊓ W) 0
      (FiniteCoverCohomology.affine_open_ext_zero (U ⊓ W) hUW M 0)
      (FiniteCoverCohomology.affine_open_ext_zero (V ⊓ W) hVW M 0))
  exact (Ext.linearEquiv₀ (C := X.Modules) (R := Γ(X,⊤))
    (X := FiniteCoverCohomology.freeOpenModule (tripleOpen U V W)) (Y := M)).symm.surjective.comp
      (freeOpenLinearEquiv M (tripleOpen U V W)).symm.surjective

def openSectionExt (M : X.Modules) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule U) M 0 := by
  let sectionEquiv : (FiniteCoverCohomology.freeOpenModule U ⟶ M) ≃ₗ[Γ(X,⊤)]
      OpenSections M U := freeOpenLinearEquiv M U
  exact sectionEquiv.symm.trans (Ext.linearEquiv₀ (C := X.Modules)
    (X := FiniteCoverCohomology.freeOpenModule U) (Y := M)).symm

lemma openSectionExt_restrict (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (x : OpenSections M V) :
    openSectionExt M U (openRestriction M h x) =
      (Ext.mk₀ (freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE h))).comp
        (openSectionExt M V x) (zero_add 0) := by
  have he : (freeOpenLinearEquiv M U).symm (openRestriction M h x) =
      freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE h) ≫ (freeOpenLinearEquiv M V).symm x := by
    apply (freeOpenLinearEquiv M U).injective
    rw [LinearEquiv.apply_symm_apply, freeOpenLinearEquiv_naturality,
      LinearEquiv.apply_symm_apply]
  exact (congrArg (Ext.mk₀ (C := X.Modules)) he).trans
    (Ext.mk₀_comp_mk₀ (C := X.Modules) _ _).symm

lemma tripleSectionBoundary_apply (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (tripleOpen U V W)) :
    tripleSectionBoundary M U V W x =
      openBoundary M (U ⊔ V) W 1
        ((Ext.mk₀ (overlapIso U V W).inv).comp
          (openBoundary M (U ⊓ W) (V ⊓ W) 0 (openSectionExt M _ x)) (zero_add 1)) := rfl

lemma tripleSectionBoundary_left (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (U ⊓ W)) :
    tripleSectionBoundary M U V W
      (openRestriction M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left) x) = 0 := by
  have hx := openSectionExt_restrict M
    (show tripleOpen U V W ≤ U ⊓ W from inf_le_left) x
  have hb := openBoundary_left M (U ⊓ W) (V ⊓ W) 0
    (openSectionExt M (U ⊓ W) x)
  rw [tripleSectionBoundary_apply]
  have he := (congrArg (openBoundary M (U ⊓ W) (V ⊓ W) 0) hx).trans hb
  dsimp only [tripleOpen] at he
  let F := (openBoundary M (U ⊔ V) W 1).comp
    (extSourceIso (overlapIso U V W) M 1).toLinearMap
  exact (congrArg F he).trans F.map_zero

lemma tripleSectionBoundary_right (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (V ⊓ W)) :
    tripleSectionBoundary M U V W
      (openRestriction M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right) x) = 0 := by
  have hx := openSectionExt_restrict M
    (show tripleOpen U V W ≤ V ⊓ W from inf_le_right) x
  have hb := openBoundary_right M (U ⊓ W) (V ⊓ W) 0
    (openSectionExt M (V ⊓ W) x)
  rw [tripleSectionBoundary_apply]
  have he := (congrArg (openBoundary M (U ⊓ W) (V ⊓ W) 0) hx).trans hb
  dsimp only [tripleOpen] at he
  let F := (openBoundary M (U ⊔ V) W 1).comp
    (extSourceIso (overlapIso U V W) M 1).toLinearMap
  exact (congrArg F he).trans F.map_zero

lemma tripleSectionBoundary_top (M : X.Modules) (U V W : X.Opens)
    (x : OpenSections M (U ⊓ V)) :
    tripleSectionBoundary M U V W
      (openRestriction M (show tripleOpen U V W ≤ U ⊓ V from
        inf_le_inf inf_le_left inf_le_left) x) = 0 := by
  have hx := openSectionExt_restrict M
    (show tripleOpen U V W ≤ U ⊓ V from inf_le_inf inf_le_left inf_le_left) x
  have hn := openBoundary_natural M (show U ⊓ W ≤ U from inf_le_left)
    (show V ⊓ W ≤ V from inf_le_left) 0 (openSectionExt M (U ⊓ V) x)
  have he : (overlapIso U V W).inv ≫
      freeOpenMap (X := X.carrier) X.ringCatSheaf
        (homOfLE (sup_le_sup (show U ⊓ W ≤ U from inf_le_left)
          (show V ⊓ W ≤ V from inf_le_left))) =
      freeOpenMap (X := X.carrier) X.ringCatSheaf (homOfLE (show (U ⊔ V) ⊓ W ≤ U ⊔ V from
        inf_le_left)) := by
    change (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).map _ ≫
      (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).map _ = _
    rw [← Functor.map_comp]
    rfl
  dsimp only [tripleOpen] at hx
  rw [tripleSectionBoundary_apply]
  erw [hx, hn, Ext.mk₀_comp_mk₀_assoc, he]
  exact openBoundary_left M (U ⊔ V) W 1 (openBoundary M U V 0 (openSectionExt M _ x))

def tripleChartImage (M : X.Modules) (U V W : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (tripleOpen U V W)) :=
  ((openRestriction M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
   (openRestriction M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range) ⊔
   (openRestriction M (show tripleOpen U V W ≤ U ⊓ V from
      inf_le_inf inf_le_left inf_le_left)).range

lemma tripleChartImage_le_ker (M : X.Modules) (U V W : X.Opens) :
    tripleChartImage M U V W ≤ (tripleSectionBoundary M U V W).ker := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨x,rfl⟩
    exact tripleSectionBoundary_left M U V W x
  · rintro _ ⟨x,rfl⟩
    exact tripleSectionBoundary_right M U V W x
  · rintro _ ⟨x,rfl⟩
    exact tripleSectionBoundary_top M U V W x

def tripleCokernelBoundary (M : X.Modules) (U V W : X.Opens) :
    (OpenSections M (tripleOpen U V W) ⧸ tripleChartImage M U V W) →ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W)) M 2 :=
  (tripleChartImage M U V W).liftQ (tripleSectionBoundary M U V W)
    (tripleChartImage_le_ker M U V W)

theorem tripleCokernelBoundary_surjective [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (hUW : IsAffineOpen (U ⊓ W)) (hVW : IsAffineOpen (V ⊓ W)) :
    Function.Surjective (tripleCokernelBoundary M U V W) := by
  intro x
  obtain ⟨y,hy⟩ := tripleSectionBoundary_surjective M U V W hU hV hW hUV hUW hVW x
  exact ⟨(tripleChartImage M U V W).mkQ y,hy⟩

def tripleCohomologyTwo (M : X.Modules) (U V W : X.Opens)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    (OpenSections M (tripleOpen U V W) ⧸ tripleChartImage M U V W) →ₗ[Γ(X,⊤)]
      cohomology M 2 := by
  let F := tripleCokernelBoundary M U V W
  let e : FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W) ≅ structureSheaf X :=
    (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).mapIso (eqToIso hc) ≪≫
    FreeOpenUnit.freeTopIso X.ringCatSheaf
  exact (extSourceIso e M 2).toLinearMap.comp F

theorem tripleCohomologyTwo_surjective [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (hUW : IsAffineOpen (U ⊓ W)) (hVW : IsAffineOpen (V ⊓ W))
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    Function.Surjective (tripleCohomologyTwo M U V W hc) := by
  let e : FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W) ≅ structureSheaf X :=
    (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).mapIso (eqToIso hc) ≪≫
    FreeOpenUnit.freeTopIso X.ringCatSheaf
  intro x
  obtain ⟨y, hy⟩ := (extSourceIso e M 2).surjective x
  obtain ⟨z, hz⟩ :=
    tripleCokernelBoundary_surjective M U V W hU hV hW hUV hUW hVW y
  refine ⟨z, ?_⟩
  change extSourceIso e M 2 (tripleCokernelBoundary M U V W z) = x
  rw [hz]
  exact hy

end
end MaximalSeshadri.Geometry

end

end OAI

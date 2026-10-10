import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.FiniteCover
import OAI.AlgebraicGeometry.Seshadri.Divisors.OpenSectionsLinear
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ExtCokernel

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque

variable {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

local instance curveCechFreeHomGroup (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance curveCechFreeHomModule (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _

def twoChartImage (M : X.Modules) (U V : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
  (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
  (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range

lemma twoChartImage_eq (M : X.Modules) (U V : X.Opens) :
    (LinearMap.range (Linear.leftComp (C := X.Modules)
      (X := FiniteCoverCohomology.freeOpenModule (U ⊓ V))
      (Y := FiniteCoverCohomology.freeOpenModule U ⊞
        FiniteCoverCohomology.freeOpenModule V) Γ(X,⊤) M
      (ModuleMayerVietoris.shortComplex (X := X.carrier) X.ringCatSheaf U V).f)).map
      (freeOpenLinearEquiv M (U ⊓ V)).toLinearMap = twoChartImage M U V := by
  let P := twoChartImage M U V
  let leftMap : FiniteCoverCohomology.freeOpenModule (U ⊓ V) ⟶
      FiniteCoverCohomology.freeOpenModule U :=
    freeOpenMap X.ringCatSheaf (homOfLE inf_le_left)
  let rightMap : FiniteCoverCohomology.freeOpenModule (U ⊓ V) ⟶
      FiniteCoverCohomology.freeOpenModule V :=
    freeOpenMap X.ringCatSheaf (homOfLE inf_le_right)
  let sectionEquiv : (FiniteCoverCohomology.freeOpenModule (U ⊓ V) ⟶ M) ≃ₗ[Γ(X,⊤)]
      OpenSections M (U ⊓ V) := freeOpenLinearEquiv M (U ⊓ V)
  have leftNaturality (morphism : FiniteCoverCohomology.freeOpenModule U ⟶ M) :
      sectionEquiv (leftMap ≫ morphism) =
        openRestriction M inf_le_left (freeOpenLinearEquiv M U morphism) :=
    freeOpenLinearEquiv_naturality M inf_le_left morphism
  have rightNaturality (morphism : FiniteCoverCohomology.freeOpenModule V ⟶ M) :
      sectionEquiv (rightMap ≫ morphism) =
        openRestriction M inf_le_right (freeOpenLinearEquiv M V morphism) :=
    freeOpenLinearEquiv_naturality M inf_le_right morphism
  apply le_antisymm
  · rintro x ⟨f,⟨g,rfl⟩,rfl⟩
    have he : biprod.lift leftMap (-rightMap) ≫ g =
        leftMap ≫ (biprod.inl ≫ g) - rightMap ≫ (biprod.inr ≫ g) := by
      simp only [biprod.lift_eq,
        Preadditive.add_comp, Category.assoc, Preadditive.neg_comp, sub_eq_add_neg]
    change sectionEquiv (biprod.lift leftMap (-rightMap) ≫ g) ∈ P
    rw [he, map_sub, leftNaturality, rightNaturality]
    exact P.sub_mem
      ((show (openRestriction M inf_le_left).range ≤ P from le_sup_left)
        ((openRestriction M inf_le_left).mem_range_self _))
      ((show (openRestriction M inf_le_right).range ≤ P from le_sup_right)
        ((openRestriction M inf_le_right).mem_range_self _))
  · apply sup_le
    · rintro x ⟨a,rfl⟩
      let morphism : FiniteCoverCohomology.freeOpenModule U ⟶ M :=
        (freeOpenLinearEquiv M U).symm a
      refine ⟨_, ⟨biprod.desc morphism 0,rfl⟩, ?_⟩
      change sectionEquiv (biprod.lift leftMap (-rightMap) ≫
        biprod.desc morphism 0) = _
      rw [biprod.lift_desc, comp_zero, add_zero, leftNaturality]
      exact congrArg (openRestriction M inf_le_left)
        ((freeOpenLinearEquiv M U).apply_symm_apply a)
    · rintro x ⟨b,rfl⟩
      let morphism : FiniteCoverCohomology.freeOpenModule V ⟶ M :=
        (freeOpenLinearEquiv M V).symm b
      refine ⟨_, ⟨biprod.desc 0 (-morphism),rfl⟩, ?_⟩
      change sectionEquiv (biprod.lift leftMap (-rightMap) ≫
        biprod.desc 0 (-morphism)) = _
      rw [biprod.lift_desc, comp_zero, zero_add, Preadditive.neg_comp,
        Preadditive.comp_neg, neg_neg, rightNaturality]
      exact congrArg (openRestriction M inf_le_right)
        ((freeOpenLinearEquiv M V).apply_symm_apply b)

def twoAffineUnionExtOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule (U ⊔ V)) M 1 := by
  have hmid (y : Ext.{1} (C := X.Modules)
      (FiniteCoverCohomology.freeOpenModule U ⊞ FiniteCoverCohomology.freeOpenModule V) M 1) :
      y = 0 := by
    apply (Ext.biprodAddEquiv (C := X.Modules)).injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        FiniteCoverCohomology.affine_open_ext_zero U hU M 0
          ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        FiniteCoverCohomology.affine_open_ext_zero V hV M 0
          ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  let complex : ShortComplex X.Modules :=
    ModuleMayerVietoris.shortComplex X.ringCatSheaf U V
  let sectionEquiv : (complex.X₁ ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M (U ⊓ V) :=
    freeOpenLinearEquiv M (U ⊓ V)
  let e := Submodule.Quotient.equiv (LinearMap.range
      (Linear.leftComp Γ(X,⊤) M complex.f)) (twoChartImage M U V) sectionEquiv
    (twoChartImage_eq M U V)
  exact e.symm.trans (ExtCokernel.quotientEquiv (C := X.Modules) (S := complex)
    (ModuleMayerVietoris.shortComplex_shortExact X.ringCatSheaf U V) M hmid)

def extSourceIso {E F : X.Modules} (e : E ≅ F) (M : X.Modules) (n : ℕ) :
    Ext.{1} E M n ≃ₗ[Γ(X,⊤)] Ext.{1} F M n where
  toFun := (Ext.mk₀ e.inv).precompOfLinear Γ(X,⊤) M (zero_add n)
  invFun := (Ext.mk₀ e.hom).precompOfLinear Γ(X,⊤) M (zero_add n)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

def twoAffineCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)] cohomology M 1 := by
  let e := twoAffineUnionExtOne M U V hU hV
  rw [hcover] at e
  exact e.trans (extSourceIso (FreeOpenUnit.freeTopIso X.ringCatSheaf) M 1)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI

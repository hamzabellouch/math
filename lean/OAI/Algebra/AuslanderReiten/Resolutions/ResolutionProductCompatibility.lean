import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

theorem conjugate_comp_of_eq {X Y : DerivedCategory C} (e : X ≅ Y)
    {n m r : ℤ} (f : ShiftedHom X X n) (g : ShiftedHom X X m) (h : m+n=r) :
    conjugate e (f.comp g h) = (conjugate e f).comp (conjugate e g) h := by
  obtain rfl : r=n+m := by omega
  exact conjugate_comp e f g

omit [HasDerivedCategory C] in
theorem cocycleHom_comp {K L M : CochainComplex C ℤ} {i j l : ℤ} (hl : i+j=l)
    (x : Cocycle K L i) (y : Cocycle L M j) (z : Cocycle K M l)
    (hz : z.val = x.val.comp y.val hl) :
    Cocycle.equivHomShift.symm z =
      ShiftedHom.comp (Cocycle.equivHomShift.symm x) (Cocycle.equivHomShift.symm y) (by omega) := by
  subst l
  have he : z = CompleteComparison.cocycleProduct x y := Subtype.ext hz
  subst z
  exact CompleteComparison.cocycleHom_product x y

def natCocycleProduct {K L M : CochainComplex C ℤ} {n m : ℕ}
    (x : Cocycle K L (n : ℤ)) (y : Cocycle L M (m : ℤ)) :
    Cocycle K M ((n+m : ℕ) : ℤ) :=
  Cocycle.mk (x.val.comp y.val (by omega)) _ rfl (by
    rw [δ_comp x.val y.val (by omega) ((n : ℤ)+1) ((m : ℤ)+1)
      (((n+m : ℕ) : ℤ)+1) rfl rfl rfl]
    simp)

variable [HasExt.{v} C]

theorem endExt_product {X : C} (P : ProjectiveResolution X) {n m : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ))
    (y : Cocycle P.cochainComplex P.cochainComplex (m : ℤ)) :
    (endExt P x).comp (endExt P y) rfl = endExt P (natCocycleProduct x y) := by
  apply Ext.homEquiv.injective
  change ((endExt P x).comp (endExt P y) rfl).hom = (endExt P (natCocycleProduct x y)).hom
  simp only [Ext.comp_hom, endExt_hom]
  rw [cocycleHom_comp (by omega) x y (natCocycleProduct x y) rfl,
    ShiftedHom.map_comp]
  exact (conjugate_comp_of_eq _ _ _ _).symm

theorem endExt_eq_augmented {X : C} (P : ProjectiveResolution X) {n : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ)) :
    endExt P x = P.extEquivCohomologyClass.symm
      (CohomologyClass.mk (x.postcomp P.π')) := by
  apply Ext.homEquiv.injective
  change (endExt P x).hom = (P.extEquivCohomologyClass.symm (CohomologyClass.mk (x.postcomp P.π'))).hom
  rw [endExt_hom, P.extEquivCohomologyClass_symm_mk_hom]
  rw [Cocycle.equivHomShift_symm_postcomp]
  rw [← ShiftedHom.comp_mk₀ _ 0 rfl, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [conjugate, resolutionIso, Iso.trans_inv, Iso.trans_hom,
    asIso_inv, asIso_hom, Functor.map_comp, Category.assoc]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI

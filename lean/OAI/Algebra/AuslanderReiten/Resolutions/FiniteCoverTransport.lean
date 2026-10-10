import OAI.Algebra.AuslanderReiten.Resolutions.FiniteCoverProducts

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u v w
section General
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L : CochainComplex C ℤ}

theorem fullHomShiftedHomotopyEquiv_ofHom (f : K ⟶ L) :
    fullHomShiftedHomotopyEquiv k K L 0 (CohomologyClass.mk (Cocycle.ofHom f)) =
      (HomotopyCategory.quotient C _).map f ≫
        (shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).inv.app
          ((HomotopyCategory.quotient C _).obj L) := by
  have h : Cocycle.equivHomShift.symm (Cocycle.ofHom f) =
      ShiftedHom.mk₀ (0 : ℤ) rfl f := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [cocycleHom_component, Cocycle.ofHom_coe]
    simp only [ShiftedHom.mk₀, HomologicalComplex.comp_f, CategoryTheory.shiftFunctorZero',
      eqToIso_refl, Iso.trans_inv, Iso.refl_inv,
      CochainComplex.shiftFunctorZero_inv_app_f, Category.comp_id]
    change (Cochain.ofHom f).v i (i+0) rfl =
      f.f i ≫ (L.XIsoOfEq (show i=i+0 by omega)).hom
    simpa only [Cochain.ofHom_v] using
      (Cochain.v_comp_XIsoOfEq_hom (Cochain.ofHom f) i i (i+0) (add_zero i) (by omega)).symm
  rw [fullHomShiftedHomotopyEquiv_mk, h]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl f).map (HomotopyCategory.quotient C _) = _
  rw [ShiftedHom.map_mk₀]
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']
end General

open scoped ModuleCat.Algebra
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]
namespace FiniteCoverTower
variable (τ : FrobeniusTrace k R) (T : FiniteCoverTower (k := k) (R := R))
variable (S : FiniteLeftModule k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

omit [CharP k 2] in
theorem coverClassFrom_hom (f : S.completeCochain τ ⟶ (T.obj 0).completeCochain τ) (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ)
      (T.coverClassFrom τ S (CohomologyClass.mk (Cocycle.ofHom f)) n) =
        (Q).map f ≫ (T.shiftIso τ n).hom := by
  induction n with
  | zero => exact fullHomShiftedHomotopyEquiv_ofHom k f
  | succ n ih =>
    change fullHomShiftedHomotopyEquiv k _ _ ((n : ℤ)+1)
      (fullHomProduct (T.coverClassFrom τ S (CohomologyClass.mk (Cocycle.ofHom f)) n)
        (T.boundaryClass τ n)) = _
    rw [fullHomShiftedHomotopyEquiv_product, ih]
    simp only [boundaryClass, LinearEquiv.apply_symm_apply]
    simp only [shiftIso, iteratedShiftIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.symm_hom, Category.assoc]
    rfl
end FiniteCoverTower
end ArExplicit

end

end OAI

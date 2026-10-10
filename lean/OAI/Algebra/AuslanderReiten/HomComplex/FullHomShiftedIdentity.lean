import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedProducts
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomDegreeProducts

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]

theorem fullHomShiftedHomotopyEquiv_identity (K : CochainComplex C ℤ) :
    fullHomShiftedHomotopyEquiv k K K 0 (fullHomIdentity K) =
      (shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).inv.app
        ((HomotopyCategory.quotient C _).obj K) := by
  have h : Cocycle.equivHomShift.symm (Cocycle.ofHom (𝟙 K)) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 K) := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [cocycleHom_component, Cocycle.ofHom_coe]
    simp only [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero',
      eqToIso_refl, Iso.trans_inv, Iso.refl_inv,
      Category.id_comp, CochainComplex.shiftFunctorZero_inv_app_f, Category.comp_id]
    change (Cochain.ofHom (𝟙 K)).v i (i+0) rfl =
      (K.XIsoOfEq (show i=i+0 by omega)).hom
    simpa only [Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp] using
      (Cochain.v_comp_XIsoOfEq_hom (Cochain.ofHom (𝟙 K)) i i (i+0) (add_zero i) (by omega)).symm
  rw [fullHomIdentity, fullHomShiftedHomotopyEquiv_mk, h]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 K)).map (HomotopyCategory.quotient C _) = _
  rw [ShiftedHom.map_mk₀, CategoryTheory.Functor.map_id]
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']

end ArExplicit

end

end OAI

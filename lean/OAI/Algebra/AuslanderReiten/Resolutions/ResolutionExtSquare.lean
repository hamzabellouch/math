import OAI.Algebra.AuslanderReiten.Ext.NatCubicExt
import OAI.Algebra.AuslanderReiten.Ext.ExtIsoCongr
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarProducts
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarIso

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {X X' Y Y' : C} (P : ProjectiveResolution X) (Q : ProjectiveResolution X')

theorem resolutionExt_square (a : X ⟶ X') (b : Y ⟶ Y')
    (φ : ProjectiveResolution.Hom P Q a) (n : ℕ)
    (f : P.complex.X n ⟶ Y) (g : Q.complex.X n ⟶ Y')
    (hf : P.complex.d (n+1) n ≫ f = 0) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (h : φ.hom.f n ≫ g = f ≫ b) :
    (Ext.mk₀ a).comp (Q.extMk g (n+1) rfl hg) (zero_add _) =
      (P.extMk f (n+1) rfl hf).comp (Ext.mk₀ b) (add_zero _) := by
  rw [ProjectiveResolution.mk₀_comp_extMk g (n+1) rfl hg φ,
    ProjectiveResolution.extMk_comp_mk₀]
  congr 1

theorem selfExtIso_eq_of_square {k : Type v} [CommRing k] [Linear k C]
    (e : X ≅ X') {n : ℕ} (x : Ext X X n) (y : Ext X' X' n)
    (h : (Ext.mk₀ e.hom).comp y (zero_add _) = x.comp (Ext.mk₀ e.hom) (add_zero _)) :
    selfExtIso (k := k) e n x = y := by
  rw [selfExtIso_apply, Ext.comp_assoc_of_third_deg_zero, ← h,
    Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
end General

end ArExplicit

end

end OAI

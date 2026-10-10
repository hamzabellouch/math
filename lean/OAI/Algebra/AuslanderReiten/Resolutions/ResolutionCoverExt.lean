import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtSquare

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {k : Type v} [CommRing k] [Linear k C]
variable {B S N : C} (P : ProjectiveResolution B) (Q : ProjectiveResolution N)

theorem resolutionExt_cover_conjugate (e : B ≅ S) (j : S ≅ N)
    (φ : ProjectiveResolution.Hom P Q (e.hom ≫ j.hom)) (n : ℕ)
    (f : P.complex.X n ⟶ S) (g : Q.complex.X n ⟶ N)
    (hf : P.complex.d (n+1) n ≫ f = 0) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (h : φ.hom.f n ≫ g = f ≫ j.hom) :
    selfExtIso (k := k) j n ((Ext.mk₀ e.inv).comp
      (P.extMk f (n+1) rfl hf) (zero_add _)) = Q.extMk g (n+1) rfl hg := by
  apply selfExtIso_eq_of_square
  have he := resolutionExt_square P Q (e.hom ≫ j.hom) j.hom φ n f g hf hg h
  have hh := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add n)) he
  rw [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_assoc] at hh
  simpa only [Ext.comp_assoc_of_third_deg_zero] using hh

end ArExplicit

end

end OAI

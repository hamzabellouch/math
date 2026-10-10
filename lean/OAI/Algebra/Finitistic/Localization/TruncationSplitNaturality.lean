import OAI.Algebra.Finitistic.Localization.TwoDegreeSplitting

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding DerivedTruncation DerivedCategory
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable (X Y : D.{u,v} P) (hX : TwoDegrees X) (hY : TwoDegrees Y)

include hX hY in
/-- Ext^3 kills the only possible off-diagonal ambiguity in a truncation splitting. -/
theorem upper_to_lower_eq_zero (f : upper X ⟶ lower Y) : f = 0 := by
  have hz := shifted_hom_eq_zero P (H P 0 X) (H P (-3) Y) 3 (by omega)
    ((upperIso P X hX).inv ≫ f ≫ (lowerIso P Y hY).hom)
  apply (cancel_epi (upperIso P X hX).inv).mp
  apply (cancel_mono (lowerIso P Y hY).hom).mp
  simpa only [Category.assoc,zero_comp,comp_zero] using hz

include hX hY in
lemma truncation_split_square (sX : TruncationSplit P X) (sY : TruncationSplit P Y) (f : X ⟶ Y) :
    f ≫ sY.iso.hom = sX.iso.hom ≫ biprod.map
      ((DerivedTruncation.t.truncLT 0).map f) ((DerivedTruncation.t.truncGE 0).map f) := by
  have hix : biprod.inl ≫ sX.iso.inv = DerivedTruncation.inclusion X := by
    rw [← sX.inclusion,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hnat : (DerivedTruncation.t.truncLT 0).map f ≫ DerivedTruncation.inclusion Y =
      DerivedTruncation.inclusion X ≫ f := (DerivedTruncation.t.truncLTι 0).naturality f
  have hpnat : f ≫ DerivedTruncation.projection Y =
      DerivedTruncation.projection X ≫ (DerivedTruncation.t.truncGE 0).map f :=
    (DerivedTruncation.t.truncGEπ 0).naturality f
  have hxy : DerivedTruncation.inclusion X ≫ f ≫ sY.iso.hom =
      (DerivedTruncation.t.truncLT 0).map f ≫ biprod.inl := by
    rw [← Category.assoc,← hnat,Category.assoc,sY.inclusion]
  apply (cancel_epi sX.iso.inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · simp only [← Category.assoc,hix]
      simpa only [Category.assoc,biprod.map_fst,biprod.inl_fst_assoc,biprod.inl_fst,Category.comp_id]
        using congrArg (fun a => a ≫ biprod.fst) hxy
    · simp only [Category.assoc,biprod.map_fst,biprod.inr_fst_assoc,zero_comp]
      exact upper_to_lower_eq_zero P X Y hX hY _
  · simp only [Category.assoc,biprod.map_snd]
    rw [← sY.projection,hpnat,sX.projection]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]

/-- The chosen actual splitting commutes with every morphism of two-degree objects. -/
theorem truncationSplit_naturality (f : X ⟶ Y) :
    f ≫ (truncationSplit P Y hY).iso.hom = (truncationSplit P X hX).iso.hom ≫ biprod.map
      ((DerivedTruncation.t.truncLT 0).map f) ((DerivedTruncation.t.truncGE 0).map f) :=
  truncation_split_square P X Y hX hY (truncationSplit P X hX) (truncationSplit P Y hY) f
end LittleFinitistic.TwoDegreeFormality

end

end OAI

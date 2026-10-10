import OAI.Algebra.Finitistic.Rectification.RectificationTotal

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
namespace LittleFinitistic.ZeroColumnTotal
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

def biprodInrIso {X Y : D} (hX : IsZero X) : Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  hom_inv_id := by simp
  inv_hom_id := by
    apply biprod.hom_ext
    · exact hX.eq_of_tgt _ _
    · simp

omit [HasBinaryBiproducts D] in
theorem complex_zero {X : CochainComplex D ℤ} (hX : ∀ i, IsZero (X.X i)) : IsZero X := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext i
  exact (hX i).eq_of_src _ _

/-- If the cone source is zero, its original inclusion is an isomorphism. -/
theorem cone_inr_isIso {X Y : CochainComplex D ℤ} (f : X ⟶ Y) (hX : IsZero X) :
    IsIso (mappingCone.inr f) := by
  have hi : ∀ i, IsIso ((mappingCone.inr f).f i) := by
    intro i
    let e : (mappingCone f).X i ≅ X.X (i+1) ⊞ Y.X i :=
      homotopyCofiber.XIsoBiprod f i (i+1) (by simp)
    rw [← isIso_comp_right_iff ((mappingCone.inr f).f i) e.hom]
    have he : (mappingCone.inr f).f i ≫ e.hom = biprod.inr :=
      homotopyCofiber.inrX_XIsoBiprod_hom f (i+1) i (by simp)
    rw [he]
    exact (biprodInrIso ((HomologicalComplex.eval D (.up ℤ) (i+1)).map_isZero hX)).isIso_hom
  let := hi
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A mapped cone whose two columns vanish is actually zero. -/
theorem mappedCone_zero {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (F : C ⥤ D) [F.Additive]
    (hX : ∀ i, IsZero (F.obj (X.X i))) (hY : ∀ i, IsZero (F.obj (Y.X i))) :
    IsZero ((F.mapHomologicalComplex (.up ℤ)).obj (mappingCone f)) := by
  apply (mappingCone.mapHomologicalComplexIso f F).isZero_iff.mpr
  apply complex_zero
  intro i
  rw [mappingCone.isZero_X_iff]
  exact ⟨hX (i+1),hY i⟩

/-- Vanishing higher columns make the original zero-column inclusion an isomorphism. -/
theorem mapped_inclusion_isIso {L₀ L₁ L₂ : CochainComplex C ℤ}
    (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁) (h : Homotopy (q ≫ p) 0)
    (F : C ⥤ D) [F.Additive]
    (h₁ : ∀ i, IsZero (F.obj (L₁.X i))) (h₂ : ∀ i, IsZero (F.obj (L₂.X i))) :
    IsIso ((F.mapHomologicalComplex (.up ℤ)).map (RectificationTotal.inclusion p q h)) := by
  let t := RectificationTotal.rectifyingMap p q h
  change IsIso ((F.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr t))
  rw [← isIso_comp_right_iff _ (mappingCone.mapHomologicalComplexIso t F).hom,
    mappingCone.map_inr]
  exact cone_inr_isIso _ (mappedCone_zero q F h₂ h₁)
end LittleFinitistic.ZeroColumnTotal

end

end OAI

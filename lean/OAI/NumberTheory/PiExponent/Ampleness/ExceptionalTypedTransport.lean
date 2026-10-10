import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque
private abbrev schemeFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

variable {A : Type} [CommRing A] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (L : LineBundle Y)

theorem frame_nonempty_of_open {U : Y.Opens} (h : U = j.opensRange)
    (he : Nonempty (L.sheaf.restrict U.ι ≅ O U.toScheme)) :
    Nonempty (Frame j L) := by
  subst U
  exact he

def transportSections (n : ℕ) {V : Y.Opens} (h : j.opensRange = V) :
    (schemeFreeOpen Y V ⟶ (L.pow n).sheaf) ≃+ Sections j L n where
  toFun b := freeOpenMap Y.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap Y.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  right_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

theorem transportSections_apply (n : ℕ) {V : Y.Opens} (h : j.opensRange = V)
    (b : schemeFreeOpen Y V ⟶ (L.pow n).sheaf) :
    transportSections j L n h b = freeOpenMap Y.ringCatSheaf (eqToHom h) ≫ b := rfl

end
end PiExponent.ExceptionalRepresentedTypes

end OAI

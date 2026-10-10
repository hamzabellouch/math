import OAI.NumberTheory.PiExponent.Approximation.GlobalSectionClearing

namespace OAI

namespace PiExponent.SheafSectionGluing
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponent.GlobalSectionClearing
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

def mapSection (f : P ⟶ Q) (U : X.Opens) :
    OpenSections P U →ₗ[Γ(X,⊤)] OpenSections Q U where
  toFun := f.app U
  map_add' := map_add _
  map_smul' r x := by
    exact f.app_smul (r := restrictScalar X U r) (x := x)

lemma mapSection_naturality (f : P ⟶ Q) {U V : X.Opens} (h : U ≤ V)
    (x : OpenSections P V) :
    mapSection f U (openRestriction P h x) = openRestriction Q h (mapSection f V x) :=
  CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE h).op) x

@[simp] lemma mapSection_comp {R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R)
    (U : X.Opens) (x : OpenSections P U) :
    mapSection (f ≫ g) U x = mapSection g U (mapSection f U x) := rfl

lemma mapSection_congr (f : P ⟶ Q) {U V : X.Opens} (h : U = V)
    (x : OpenSections P U) :
    openSectionsCongr Q h (mapSection f U x) = mapSection f V (openSectionsCongr P h x) := by
  subst V
  rfl

theorem glue_after_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i j,
      mapSection f (U i ⊓ U j) (openRestriction P inf_le_left (y i)) =
        mapSection f (U i ⊓ U j) (openRestriction P inf_le_right (y j))) :
    ∃ z : OpenSections Q ⊤,
      ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i) := by
  have h := TopCat.Sheaf.existsUnique_gluing' ⟨_, Q.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover])
    (fun i => mapSection f (U i) (y i)) ?_
  · obtain ⟨z, hz, _⟩ := h
    exact ⟨z, hz⟩
  · intro i j
    change openRestriction Q (show U i ⊓ U j ≤ U i from inf_le_left) (mapSection f (U i) (y i)) =
      openRestriction Q (show U i ⊓ U j ≤ U j from inf_le_right) (mapSection f (U j) (y j))
    rw [← mapSection_naturality, ← mapSection_naturality]
    exact hy i j

theorem restriction_of_glued_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (D : X.Opens) (x : OpenSections P D)
    (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x)
    (z : OpenSections Q ⊤)
    (hz : ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i)) :
    openRestriction Q (show D ≤ ⊤ from le_top) z = mapSection f D x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, Q.isSheaf⟩ (fun i => U i ⊓ D) D
    (fun i => homOfLE inf_le_right) (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction Q inf_le_right (openRestriction Q (show D ≤ ⊤ from le_top) z) =
    openRestriction Q inf_le_right (mapSection f D x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply Q (show U i ⊓ D ≤ U i from inf_le_left) le_top z,
    hz i, ← mapSection_naturality, hy i, mapSection_naturality]

theorem overlap_difference_zero {ι : Type*} (U : ι → X.Opens) (D : X.Opens)
    (x : OpenSections P D) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x) (i j : ι) :
    openRestriction P (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ U j from inf_le_left)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 := by
  rw [map_sub, openRestriction_comp_apply, openRestriction_comp_apply]
  have hi := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ D from inf_le_inf inf_le_left le_rfl)) (hy i)
  have hj := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U j ⊓ D from inf_le_inf inf_le_right le_rfl)) (hy j)
  simp only [openRestriction_comp_apply] at hi hj
  rw [hi, hj, sub_self]

end
end PiExponent.SheafSectionGluing

end OAI

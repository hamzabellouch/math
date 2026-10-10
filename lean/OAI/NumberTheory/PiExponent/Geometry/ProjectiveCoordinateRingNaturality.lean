import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartRingNaturality
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFiniteSections

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
lemma isoPreimageSectionRingEquiv_symm (X Y : Scheme) (f : X ≅ Y) (V : Y.Opens)
    (a : Γ(Y,V)) :
    (isoPreimageSectionRingEquiv f V).symm a = f.hom.app V a := by
  change (((IsOpenImmersion.ΓIso f.hom V) ≪≫
    Y.presheaf.mapIso (eqToIso (show V = f.hom.opensRange ⊓ V by
      rw [Scheme.Hom.opensRange_of_isIso, top_inf_eq])).op).inv).hom a = _
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    IsOpenImmersion.ΓIso_inv, Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]

lemma isoPreimageSectionRingEquiv_appLE {X Y : Scheme} (f : X ≅ Y)
    (V : Y.Opens) (U : X.Opens) (h : U = f.hom ⁻¹ᵁ V) (a : Γ(Y,V)) :
    (isoPreimageSectionRingEquiv f V)
      (X.presheaf.map (eqToHom h.symm).op (f.hom.appLE V U h.le a)) = a := by
  subst U
  simpa [Scheme.Hom.appLE_eq_app, isoPreimageSectionRingEquiv_symm] using
    (isoPreimageSectionRingEquiv f V).apply_symm_apply a

lemma appLE_restrict_comm {X Y : Scheme} (f : X ⟶ Y)
    {U V : Y.Opens} {U' V' : X.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (eU : U' ≤ f ⁻¹ᵁ U) (eV : V' ≤ f ⁻¹ᵁ V) (x : Γ(Y,U)) :
    X.presheaf.map (homOfLE h').op (f.appLE U U' eU x) =
      f.appLE V V' eV (Y.presheaf.map (homOfLE h).op x) := by
  change (f.appLE U U' eU ≫ X.presheaf.map (homOfLE h').op) x =
    (Y.presheaf.map (homOfLE h).op ≫ f.appLE V V' eV) x
  simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
lemma coordinateSectionChartIso_factor (i : σ) :
    (coordinateSectionChartIso M k s hc f hf i).hom =
      f.hom.resLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le ≫
      (Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)).hom := by
  apply (cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i)
    (poly_X_mem i) (by decide))).1
  rw [coordinateSectionChartIso_hom_away, hf]
  simp only [Category.assoc, Proj.awayι, Iso.hom_inv_id_assoc,
    Scheme.Hom.resLE_comp_ι]
lemma coordinateSectionChartIso_pullback (i : σ) :
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      (coordinateSectionChartIso M k s hc f hf i).hom.appTop ≫
        (SectionOpens.isoOpen (s i)).topIso.hom =
    Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) ≫
      f.hom.appLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le := by
  rw [coordinateSectionChartIso_factor, Scheme.Hom.comp_appTop]
  simp only [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
    Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

lemma coordinateSectionRingEquiv_symm (i : σ) (p : MvPolynomial (ChartVariables i) K) :
    (coordinateSectionRingEquiv M k s hc f hf i).symm p =
      f.hom.appLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le
        (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p)) := by
  exact congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (polyToChart i p)) (coordinateSectionChartIso_pullback M k s hc f hf i)

lemma coordinateFiniteRingEquiv_appLE (i : σ) (a : Finset (ChartVariables i))
    (x : Γ(Proj (PolyGrade K σ),
      Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ⊓
        a.inf (fun j => Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X j.val)))) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le x) =
      chartVariableOverlapRingEquiv i a x := by
  change chartVariableOverlapRingEquiv i a
    (isoPreimageSectionRingEquiv f _
      (X.presheaf.map (eqToHom (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).symm).op
        (f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le x))) = _
  rw [isoPreimageSectionRingEquiv_appLE f _ _
    (coordinateFiniteOpen_eq_preimage M s k hc f hf i a)]

lemma coordinateFiniteRingEquiv_restrict (i : σ) (a : Finset (ChartVariables i))
    (p : MvPolynomial (ChartVariables i) K) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((coordinateSectionRingEquiv M k s hc f hf i).symm p)) =
      algebraMap _ _ p := by
  rw [coordinateSectionRingEquiv_symm]
  have h : X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
      (f.hom.appLE _ _ (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le
        (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p))) =
      f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le
        ((Proj (PolyGrade K σ)).presheaf.map (homOfLE inf_le_left).op
          (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p))) := by
    exact appLE_restrict_comm f.hom inf_le_left inf_le_left _ _ _
  rw [h, coordinateFiniteRingEquiv_appLE, chartVariableOverlapRingEquiv_restrict]
  rfl

end

end Projective
end PiExponentSeshadri

end OAI

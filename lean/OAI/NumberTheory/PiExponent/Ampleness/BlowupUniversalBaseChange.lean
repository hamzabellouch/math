import OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.hom_ext (hπ : IsBlowup I π) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) {g h : Y ⟶ B}
    (hg : g ≫ π = f) (hh : h ≫ π = f) : g = h := by
  obtain ⟨l, _, hl⟩ := hπ.2 Y f hf
  exact (hl g hg).trans (hl h hh).symm

lemma IsBlowup.postIso (hπ : IsBlowup I π) (e : X ≅ Z)
    (J : Z.IdealSheafData) (he : J.comap e.hom = I) :
    IsBlowup J (π ≫ e.hom) := by
  have hcongr (W : Scheme) (f : W ⟶ X) :
      InvertiblePullbackIdeal J (f ≫ e.hom) ↔ InvertiblePullbackIdeal I f :=
    InvertibleLocal.invertible_congr (by rw [Scheme.IdealSheafData.comap_comp, he])
  refine ⟨(hcongr B π).mpr hπ.1, ?_⟩
  intro W f hf
  have hf' : InvertiblePullbackIdeal I (f ≫ e.inv) := by
    apply (hcongr W (f ≫ e.inv)).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ e.inv) hf'
  refine ⟨l, ?_, ?_⟩
  · change l ≫ π ≫ e.hom = f
    rw [← Category.assoc, hl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    apply huniq m
    rw [← cancel_mono e.hom, Category.assoc, hm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

lemma IsBlowup.open_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_restrict_general I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

def IsBlowup.iso {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : B ≅ B' where
  hom := (hπ'.2 B π hπ.1).choose
  inv := (hπ.2 B' π' hπ'.1).choose
  hom_inv_id := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, (hπ.2 B' π' hπ'.1).choose_spec.1]
      exact (hπ'.2 B π hπ.1).choose_spec.1
    · simp
  inv_hom_id := by
    apply hπ'.hom_ext π' hπ'.1
    · rw [Category.assoc, (hπ'.2 B π hπ.1).choose_spec.1]
      exact (hπ.2 B' π' hπ'.1).choose_spec.1
    · simp

@[reassoc (attr := simp)]
lemma IsBlowup.iso_hom_comp {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : (hπ.iso hπ').hom ≫ π' = π :=
  (hπ'.2 B π hπ.1).choose_spec.1

end

section
variable {X B B' Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.baseChangeSquare (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] (ρ : B' ⟶ Z) (hρ : IsBlowup (I.comap j) ρ)
    (β : B' ⟶ B) (hβ : β ≫ π = ρ ≫ j) : IsPullback ρ β j π := by
  let e := hρ.iso (hπ.open_baseChange j)
  refine IsPullback.of_iso_pullback ⟨hβ.symm⟩ e
    (hρ.iso_hom_comp (hπ.open_baseChange j)) ?_
  apply hπ.hom_ext (ρ ≫ j)
  · exact (InvertibleLocal.invertible_congr
      (Scheme.IdealSheafData.comap_comp I ρ j)).mpr hρ.1
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      hρ.iso_hom_comp (hπ.open_baseChange j)]
  · exact hβ

end

open TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B B' : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.preIso (hπ : IsBlowup I π) (e : B' ≅ B) :
    IsBlowup I (e.hom ≫ π) := by
  refine ⟨InvertibleLocal.invertible_restrict_general I π hπ.1 e.hom,?_⟩
  intro Y f hf
  obtain ⟨g,hg,huniq⟩ := hπ.2 Y f hf
  refine ⟨g ≫ e.inv,by simp only [Category.assoc,Iso.inv_hom_id_assoc,hg],?_⟩
  intro g' hg'
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using huniq (g' ≫ e.hom) hg'

lemma IsBlowup.morphismRestrict (hπ : IsBlowup I π) (U : X.Opens) :
    IsBlowup (I.comap U.ι) (π ∣_ U) := by
  have H := (hπ.open_baseChange U.ι).preIso (isPullback_morphismRestrict π U).isoPullback
  rwa [(isPullback_morphismRestrict π U).isoPullback_hom_fst] at H

end
end PiExponentSeshadri.Geometry

end OAI

import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionChart

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme} {M N : X.Modules}

lemma restrictSection_postcomp (φ : Y ⟶ X) [IsOpenImmersion φ]
    (s : O X ⟶ M) (f : M ⟶ N) :
    restrictSection φ (s ≫ f) = restrictSection φ s ≫
      (Scheme.Modules.restrictFunctor φ).map f := by
  exact (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso φ).inv ≫ morphism)
    ((Scheme.Modules.restrictFunctor φ).map_comp s f)).trans (Category.assoc _ _ _).symm

def restrictEndIso (φ : Y ⟶ X) [IsOpenImmersion φ] (a : O X ≅ O X) : O Y ≅ O Y :=
  (Scheme.Modules.restrictUnitIso φ).symm ≪≫
    (Scheme.Modules.restrictFunctor φ).mapIso a ≪≫ Scheme.Modules.restrictUnitIso φ

lemma restrictSection_precomp (φ : Y ⟶ X) [IsOpenImmersion φ]
    (a : O X ≅ O X) (s : O X ⟶ M) :
    restrictSection φ (a.hom ≫ s) = (restrictEndIso φ a).hom ≫ restrictSection φ s := by
  let restriction := Scheme.Modules.restrictFunctor φ
  let unitIso := Scheme.Modules.restrictUnitIso φ
  change unitIso.inv ≫ restriction.map (a.hom ≫ s) =
    (unitIso.inv ≫ restriction.map a.hom ≫ unitIso.hom) ≫
      unitIso.inv ≫ restriction.map s
  exact (restrictSection_postcomp φ a.hom s).trans
    ((congrArg (fun morphism => (unitIso.inv ≫ restriction.map a.hom) ≫ morphism)
      (unitIso.hom_inv_id_assoc (restriction.map s)).symm).trans
        ((Category.assoc (unitIso.inv ≫ restriction.map a.hom) unitIso.hom
          (unitIso.inv ≫ restriction.map s)).symm.trans
            (congrArg (fun morphism => morphism ≫ unitIso.inv ≫ restriction.map s)
              (Category.assoc unitIso.inv (restriction.map a.hom) unitIso.hom))))

lemma coefficient_precomp {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  exact (congrArg endValue (Category.assoc a s e.hom)).trans (endValue_comp _ _)

def endUnit (a : O X ≅ O X) : Γ(X, ⊤)ˣ := frameChange (Iso.refl _) a
@[simp] lemma endUnit_val (a : O X ≅ O X) : (endUnit a : Γ(X, ⊤)) = endValue a.hom := by
  simp [endUnit, frameChange]

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] {X : Scheme}

lemma twistedSections_cover {M N : X.Modules} (a : O X ≅ O X) (e : M ≅ N)
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    (⨆ i, SectionOpens.isoOpen (a.hom ≫ s i ≫ e.hom)) = ⊤ := by
  simpa only [← Category.assoc, SectionOpens.isoOpen_postcomp,
    SectionOpens.isoOpen_precomp] using hs

lemma sectionsMorphism_twist {M N : X.Modules} (k : K →+* Γ(X, ⊤))
    (a : O X ≅ O X) (e : M ≅ N) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k (fun i => a.hom ≫ s i ≫ e.hom) (twistedSections_cover a e s hs) =
      sectionsMorphism k s hs := by
  let t (i : σ) := a.hom ≫ s i ≫ e.hom
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hs).hom_ext
  intro i
  let U := SectionOpens.isoOpen (s i)
  have hU : U ≤ SectionOpens.isoOpen (t i) := by
    simp only [t, ← Category.assoc, SectionOpens.isoOpen_postcomp,
      SectionOpens.isoOpen_precomp]
    exact le_rfl
  let f := (Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ sectionFrame (s i)
  let b := sectionFrameOn (t i) U hU
  let c := frameChange f b * endUnit (restrictEndIso U.ι a)
  have hc (j : σ) : coefficient b (restrictSection U.ι (t j)) =
      (c : Γ(U.toScheme, ⊤)) * coefficient (sectionFrame (s i)) (restrictSection U.ι (s j)) := by
    rw [coefficient_change f b]
    have hh : coefficient f (restrictSection U.ι (t j)) =
        endValue (restrictEndIso U.ι a).hom *
          coefficient (sectionFrame (s i)) (restrictSection U.ι (s j)) := by
      dsimp only [f]
      rw [coefficient_transport]
      change coefficient (sectionFrame (s i))
        (restrictSection U.ι (a.hom ≫ s j ≫ e.hom) ≫
          (Scheme.Modules.restrictFunctor U.ι).map e.inv) = _
      rw [← Category.assoc a.hom, restrictSection_postcomp, Category.assoc,
        ← (Scheme.Modules.restrictFunctor U.ι).map_comp, Iso.hom_inv_id,
        (Scheme.Modules.restrictFunctor U.ι).map_id, Category.comp_id,
        restrictSection_precomp, coefficient_precomp]
    rw [hh]
    simp only [c, Units.val_mul, endUnit_val, mul_assoc]
  change U.ι ≫ sectionsMorphism k t _ = U.ι ≫ sectionsMorphism k s hs
  exact (sectionsMorphism_on k t _ i U hU).trans
    ((coordinatesMap_scale _ _ _ _ i i (sectionFrame_normalized (s i))
      (sectionFrameOn_normalized (t i) U hU) c hc).symm.trans
        (sectionsMorphism_local k s hs i).symm)

end
end MaximalSeshadri.Projective
end


end
end

end OAI

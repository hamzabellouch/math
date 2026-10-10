import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.AffineSectionQuotient

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X Y : Scheme.{0}}

def sectionRestrictionLinear (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    Γ(M,⊤) →ₛₗ[f.appTop.hom] Γ(M.restrict f,⊤) where
  toFun m := (M.restrictAppIso f ⊤).inv
    (M.presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op m)
  map_add' := by intro a b; simp only [map_add]
  map_smul' r m := by
    change (M.restrictAppIso f ⊤).inv
      (M.presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op (r • m)) = _
    rw [M.map_smul, Scheme.Modules.smul_restrictAppIso_inv_apply]
    congr 1
    have hm := Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := ⊤) (by simp)
    have hApp : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    rw [hApp] at hm
    have he := CategoryTheory.congr_fun hm r
    change (f.appIso ⊤).hom _ = f.appTop r
    rw [← he]
    exact ConcreteCategory.congr_hom (f.appIso ⊤).inv_hom_id (f.appTop r)

lemma sectionRestrictionLinear_surjective (M : X.Modules) (f : Y ⟶ X)
    [IsOpenImmersion f]
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)] :
    Function.Surjective (sectionRestrictionLinear M f) := by
  have hs : Function.Surjective
      (M.presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).mp
      (TopCat.Presheaf.IsFlasque.epi (F := ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj)
        (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op)
  exact (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).inv).surjective.comp hs

def restrictCokernelIso {M : X.Modules} (s : O X ⟶ M)
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (cokernel s).restrict f ≅ cokernel (restrictSection f s) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) s ≪≫
    cokernel.mapIso _ _ (Scheme.Modules.restrictUnitIso f) (Iso.refl _)
      (by
        let unitIso : (O X).restrict f ≅ O Y := Scheme.Modules.restrictUnitIso f
        change (Scheme.Modules.restrictFunctor f).map s ≫ 𝟙 _ =
          unitIso.hom ≫ unitIso.inv ≫ (Scheme.Modules.restrictFunctor f).map s
        rw [Category.comp_id, unitIso.hom_inv_id_assoc])

def moduleIsoTop {M N : X.Modules} (e : M ≅ N) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv x := congrArg (fun t : M ⟶ M => t.app ⊤ x) e.hom_inv_id
  right_inv x := congrArg (fun t : N ⟶ N => t.app ⊤ x) e.inv_hom_id
  map_add' := by intro a b; exact map_add _ a b
  map_smul' := by intro r m; exact e.hom.app_smul r m

lemma LineBundle.restrict_nonzero [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : restrictSection f s ≠ 0 := by
  intro h
  apply hs
  apply L.restrict_sections_injective f
  let unitIso : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi unitIso.inv).mp
  change restrictSection f s = restrictSection f 0
  simpa only [restrictSection_zero] using h

def sectionQuotientLocalMap [IsIntegral X] [IsNoetherian X]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Γ(cokernel s,⊤) →ₛₗ[f.appTop.hom]
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) := by
  letI : IsIntegral Y := isIntegral_of_isOpenImmersion f
  let E := (moduleIsoTop (restrictCokernelIso s f)).trans
    (affine_section_quotient (L.restrict f) e (restrictSection f s)
      (L.restrict_nonzero f s hs)).symm
  exact E.toLinearMap.comp (sectionRestrictionLinear (cokernel s) f)

lemma sectionQuotientLocalMap_surjective [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Surjective (sectionQuotientLocalMap L s hs f e) := by
  let : IsIntegral Y := isIntegral_of_isOpenImmersion f
  exact ((moduleIsoTop (restrictCokernelIso s f)).trans
    (affine_section_quotient (L.restrict f) e (restrictSection f s)
      (L.restrict_nonzero f s hs)).symm).surjective.comp
    (@sectionRestrictionLinear_surjective X Y (cokernel s) f _
      (L.cokernel_flasque hd s hs))

lemma baseScalars_comp_actual (f : Y ⟶ X) (g : X ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ g) = f.appTop.hom.comp (baseScalars g) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

def sectionQuotientLocalComplex [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
    letI := Module.compHom
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
    Γ(cokernel s,⊤) →ₗ[ℂ]
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) := by
  letI := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  letI := Module.compHom
    (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
  refine { toFun := sectionQuotientLocalMap L s hs f e
           map_add' := (sectionQuotientLocalMap L s hs f e).map_add
           map_smul' := ?_ }
  intro r x
  change (sectionQuotientLocalMap L s hs f e) (baseScalars p r • x) =
    baseScalars (f ≫ p) r • (sectionQuotientLocalMap L s hs f e) x
  rw [baseScalars_comp_actual]
  exact (sectionQuotientLocalMap L s hs f e).map_smulₛₗ (baseScalars p r) x

theorem projective_local_section_quotient_finite [IsIntegral X] [IsNoetherian X]
    {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    letI := Module.compHom
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
    Module.Finite ℂ (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) := by
  let := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  let := Module.compHom
    (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology (cokernel s) 0) (baseScalars p)
  let := projective_section_cokernel_finite p hd a ha L s hs 0
  let : Module.Finite ℂ Γ(cokernel s,⊤) :=
    Module.Finite.of_surjective (cohomologyZeroSections p (cokernel s)).toLinearMap
      (cohomologyZeroSections p (cokernel s)).surjective
  exact Module.Finite.of_surjective (sectionQuotientLocalComplex p L s hs f e)
    (sectionQuotientLocalMap_surjective hd.le L s hs f e)

theorem projective_local_section_length_le_degree [IsIntegral X] [IsNoetherian X]
    {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (f : Y ⟶ X) [IsOpenImmersion f] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    letI := Module.compHom
      (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
    (Module.finrank ℂ (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) : ℤ) ≤
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  let := Module.compHom Γ(cokernel s,⊤) (baseScalars p)
  let := Module.compHom
    (Γ(Y,⊤) ⧸ Ideal.span {coefficient e (restrictSection f s)}) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology (cokernel s) 0) (baseScalars p)
  let := projective_section_cokernel_finite p hd a ha L s hs 0
  let : Module.Finite ℂ Γ(cokernel s,⊤) :=
    Module.Finite.of_surjective (cohomologyZeroSections p (cokernel s)).toLinearMap
      (cohomologyZeroSections p (cokernel s)).surjective
  have hb := LinearMap.finrank_le_finrank_of_surjective
    (f := sectionQuotientLocalComplex p L s hs f e)
    (sectionQuotientLocalMap_surjective hd.le L s hs f e)
  rw [projective_section_euler_difference p hd a ha L s hs]
  exact_mod_cast hb

end
end MaximalSeshadri.Geometry

end


end
end

end OAI

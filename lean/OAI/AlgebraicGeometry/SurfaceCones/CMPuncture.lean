import OAI.AlgebraicGeometry.SurfaceCones.ModelSheaf

namespace OAI


/-! Reflexivity and punctured pullback of a finite module of depth three. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace ExplicitCone
lemma module_reflexive_from_depth_three (M : Type) [AddCommGroup M]
    [Module completedRing M] [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    Module.IsReflexive completedRing M := by
  let := actualCompletion_noetherian
  let := (module_properties_from_depth_three M hdepth).1
  obtain ⟨rs, hm, hr, hl⟩ :=
    SmallCM.exists_regularSequence_of_localDepth_eq (n := 2) hdepth
  exact CMReflexivity.reflexive_of_regular_three completedRing_dimension rs hm hr hl
end ExplicitCone
namespace SourceConeMorphism
open KummerSourceModel
abbrev punctureInclusion := (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).ι

instance punctureInclusion_comp_p_openImmersion : IsOpenImmersion (punctureInclusion ≫ p) := by
  rw [← puncturedIso_hom_ι]
  infer_instance

def E_punctureIso (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3) :
    (pullback punctureInclusion).obj (E M) ≅
      (pullback (p ∣_ ExplicitCone.completedPunctureOpen)).obj
        ((pullback ExplicitCone.completedPunctureOpen.ι).obj (tilde M)) := by
  letI := ExplicitCone.actualCompletion_noetherian
  letI := ExplicitCone.module_reflexive_from_depth_three M hdepth
  exact CMReflexiveSheaf.punctureEIso (R := CommRingCat.of ExplicitCone.completedRing) M p ExplicitCone.completedPunctureOpen
end SourceConeMorphism

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentBaseChange
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules)

def pushforwardRestrictSource : U.toScheme.Modules :=
  (restrictFunctor U.ι).obj ((pushforward f).obj M)

def pushforwardRestrictTarget : U.toScheme.Modules :=
  (pushforward (f ∣_ U)).obj ((restrictFunctor (f ⁻¹ᵁ U).ι).obj M)

/-- Finite-open restriction of pushforward, on sections. -/
def pushforwardRestrictAppIso (V : U.toScheme.Opens) :
    ((pushforwardRestrictSource f U M).val.obj (op V)) ≅
      ((pushforwardRestrictTarget f U M).val.obj (op V)) := by
  refine ModuleCat.isoMk
    (M.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V)).op) ?_
  intro r
  change M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op ≫
      M.smul (((f ⁻¹ᵁ U).ι.appIso _).inv ((f ∣_ U).app V r)) =
    M.smul (f.app _ ((U.ι.appIso V).inv r)) ≫
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rw [morphismRestrict_app]
  exact (M.map_comp_smul (eqToHom (image_morphismRestrict_preimage f U V))
    (f.app _ r)).symm

lemma pushforwardRestrictAppIso_naturality {V W : U.toScheme.Opensᵒᵖ} (g : V ⟶ W) :
    (pushforwardRestrictSource f U M).val.map g ≫
      (ModuleCat.restrictScalars (U.toScheme.ringCatSheaf.obj.map g).hom).map
        (pushforwardRestrictAppIso f U M W.unop).hom =
    (pushforwardRestrictAppIso f U M V.unop).hom ≫
      (pushforwardRestrictTarget f U M).val.map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (M.presheaf.map ((TopologicalSpace.Opens.map f.base).map
        (U.ι.opensFunctor.map g.unop)).op ≫
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op) x =
    (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op ≫
      M.presheaf.map ((f ⁻¹ᵁ U).ι.opensFunctor.map
        ((TopologicalSpace.Opens.map (f ∣_ U).base).map g.unop)).op) x
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 2

/-- Open base change for sheaves of modules; no assumption of flat base change or quasicoherence is
needed for restriction to an open. -/
def pushforwardRestrictIso :
    (restrictFunctor U.ι).obj ((pushforward f).obj M) ≅
      (pushforward (f ∣_ U)).obj ((restrictFunctor (f ⁻¹ᵁ U).ι).obj M) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => pushforwardRestrictAppIso f U M V.unop)
      (fun _ _ g => pushforwardRestrictAppIso_naturality f U M g))
end CoherentBaseChange

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

/-- A finite global presentation on an affine scheme is the associated sheaf of a finite module, via
the finite cokernel of its presentation. -/
lemma exists_finite_module_of_presentation {R : CommRingCat}
    (M : (Spec R).Modules) (P : M.Presentation) [P.IsFinite] :
    ∃ N : ModuleCat R, Module.Finite R N ∧ Nonempty (tilde N ≅ M) := by
  let : Finite P.generators.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := P)).finite
  let A := ModuleCat.of R (P.relations.I →₀ R)
  let B := ModuleCat.of R (P.generators.I →₀ R)
  let f : SheafOfModules.free P.relations.I ⟶ SheafOfModules.free P.generators.I :=
    P.relations.π ≫ kernel.ι P.generators.π
  let g : A ⟶ B := (tilde.functor R).preimage
    ((tildeFinsupp P.relations.I).hom ≫ f ≫ (tildeFinsupp P.generators.I).inv)
  let N := ModuleCat.of R (B ⧸ g.hom.range)
  have : Module.Finite R B := inferInstanceAs (Module.Finite R (P.generators.I →₀ R))
  refine ⟨N, inferInstance, ⟨?_⟩⟩
  let e : cokernel ((tilde.functor R).map g) ≅ cokernel f := by
    refine cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) ?_
    change (tilde.functor R).map g ≫ (tildeFinsupp P.generators.I).hom =
      (tildeFinsupp P.relations.I).hom ≫ f
    have hg : (tilde.functor R).map g =
        (tildeFinsupp P.relations.I).hom ≫ f ≫ (tildeFinsupp P.generators.I).inv :=
      (tilde.functor R).map_preimage _
    exact (congrArg (fun k => k ≫ (tildeFinsupp P.generators.I).hom) hg).trans
      (by
        have cancel {X Y Z T : (Spec R).Modules}
            (u : X ⟶ Y) (v : Y ⟶ Z) (e : T ≅ Z) :
            (u ≫ v ≫ e.inv) ≫ e.hom = u ≫ v := by
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact cancel (tildeFinsupp P.relations.I).hom f (tildeFinsupp P.generators.I))
  exact (tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient g).symm ≪≫
    PreservesCokernel.iso (tilde.functor R) g ≪≫ e ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) P.isColimit

lemma exists_presentation_kernel_of_presentations {R : CommRingCat} [IsNoetherianRing R]
    {M N : (Spec R).Modules} (f : M ⟶ N)
    (PM : M.Presentation) [PM.IsFinite] (PN : N.Presentation) [PN.IsFinite] :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_finite_module_of_presentation M PM
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_finite_module_of_presentation N PN
  let := hA
  let := hB
  let g := eA.hom ≫ f ≫ eB.inv
  let e : kernel f ≅ kernel g := CoherentDual.kernelConjugateIso f eA.symm eB.symm
  exact exists_presentation_iso e.symm (exists_presentation_kernel g)

lemma exists_presentation_cokernel_tilde {R : CommRingCat}
    [IsNoetherianRing R] {M N : ModuleCat R} [Module.Finite R N] (f : M ⟶ N) :
    ∃ P : (cokernel (tilde.map f)).Presentation, P.IsFinite := by
  let e : cokernel (tilde.map f) ≅ tilde (ModuleCat.of R (N ⧸ f.hom.range)) :=
    (PreservesCokernel.iso (tilde.functor R) f).symm ≪≫
      (tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient f)
  exact exists_presentation_iso e.symm (exists_presentation_tilde _)

lemma exists_presentation_cokernel_of_presentations {R : CommRingCat} [IsNoetherianRing R]
    {M N : (Spec R).Modules} (f : M ⟶ N)
    (PM : M.Presentation) [PM.IsFinite] (PN : N.Presentation) [PN.IsFinite] :
    ∃ P : (cokernel f).Presentation, P.IsFinite := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_finite_module_of_presentation M PM
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_finite_module_of_presentation N PN
  let := hA
  let := hB
  let g := eA.hom ≫ f ≫ eB.inv
  let h := (tilde.functor R).preimage g
  have hg : (tilde.functor R).map h = g := (tilde.functor R).map_preimage g
  let e : cokernel f ≅ cokernel g :=
    cokernel.mapIso _ _ eA.symm eB.symm (by simp [g])
  let e' : cokernel ((tilde.functor R).map h) ≅ cokernel g :=
    cokernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by
      change (tilde.functor R).map h = g
      exact hg)
  exact exists_presentation_iso (e' ≪≫ e.symm) (exists_presentation_cokernel_tilde h)

/-- Refine any one finite presentation chart to an arbitrary affine open inside it. This is used to
put two coherent sheaves in finite module form on the same affine cover, without assuming global
finite generation. -/
lemma exists_presentation_affine_below {X : Scheme} (M : X.Modules) (U : X.Opens)
    (P : (M.over U).Presentation) [P.IsFinite] (V : X.affineOpens) (hV : V.1 ≤ U) :
    ∃ Q : ((restrictFunctor (V.2.isoSpec.inv ≫ V.1.ι)).obj M).Presentation,
      Q.IsFinite := by
  let h : Spec Γ(X, V.1) ⟶ U.toScheme := V.2.isoSpec.inv ≫ X.homOfLE hV
  let F : SheafOfModules (X.ringCatSheaf.over U) ⥤
      SheafOfModules (Spec Γ(X, V.1)).ringCatSheaf :=
    (overEquiv U).functor ⋙ restrictFunctor h
  have : F.IsLeftAdjoint := inferInstanceAs
    ((overEquiv U).functor ⋙ restrictFunctor h).IsLeftAdjoint
  let e : SheafOfModules.unit (Spec Γ(X, V.1)).ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (restrictUnitIso h).symm ≪≫ (restrictFunctor h).mapIso
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm
  let q : F.obj (M.over U) ≅ (restrictFunctor (V.2.isoSpec.inv ≫ V.1.ι)).obj M :=
    (restrictFunctor h).mapIso ((overFunctorEquiv U).app M) ≪≫
      ((restrictFunctorComp h U.ι).app M).symm ≪≫
      (restrictFunctorCongr (by dsimp [h]; simp)).app M
  exact exists_presentation_iso q ⟨P.map F e, inferInstance⟩

lemma exists_presentation_prod_of_presentations {R : CommRingCat} [IsNoetherianRing R]
    (M N : (Spec R).Modules)
    (PM : M.Presentation) [PM.IsFinite] (PN : N.Presentation) [PN.IsFinite] :
    ∃ P : (M ⨯ N).Presentation, P.IsFinite := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_finite_module_of_presentation M PM
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_finite_module_of_presentation N PN
  let := hA
  let := hB
  let e : ModuleCat.of R (A × B) ≅ A ⨯ B :=
    IsLimit.conePointUniqueUpToIso (ModuleCat.binaryProductLimitCone A B).isLimit
      (limit.isLimit _)
  let q : tilde (ModuleCat.of R (A × B)) ≅ M ⨯ N :=
    (tilde.functor R).mapIso e ≪≫ PreservesLimitPair.iso (tilde.functor R) A B ≪≫
      prod.mapIso eA eB
  exact exists_presentation_iso q (exists_presentation_tilde _)

end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

/-- An affine common refinement of any two open covers. -/
lemma exists_common_affine_refinement {X : Scheme.{0}} {I J : Type}
    (A : I → X.Opens) (B : J → X.Opens)
    (hA : (⨆ i, A i) = ⊤) (hB : (⨆ j, B j) = ⊤) :
    ∃ (K : Type) (U : K → X.affineOpens), (⨆ k, (U k).1) = ⊤ ∧
      ∀ k, ∃ i j, (U k).1 ≤ A i ∧ (U k).1 ≤ B j := by
  let K := {V : X.affineOpens // ∃ i j, V.1 ≤ A i ∧ V.1 ≤ B j}
  refine ⟨K, fun V => V.1, ?_, fun V => V.property⟩
  apply le_antisymm le_top
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, A i by rw [hA]; trivial)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ j, B j by rw [hB]; trivial)
  obtain ⟨V, hV, hxV, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := A i ⊓ B j) (x := x) ⟨hi, hj⟩
  let v : K := ⟨⟨V, hV⟩, i, j, fun y hy => (hsub hy).1, fun y hy => (hsub hy).2⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨v, hxV⟩

/-- Two coherent sheaves admit finite module presentations on the same affine open cover. No global
generation assumption is imposed. -/
lemma exists_common_affine_presentations {X : Scheme.{0}} (M N : X.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation] :
    ∃ (I : Type) (U : I → X.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i,
      (∃ P : ((restrictFunctor ((U i).2.isoSpec.inv ≫ (U i).1.ι)).obj M).Presentation,
        P.IsFinite) ∧
      (∃ P : ((restrictFunctor ((U i).2.isoSpec.inv ≫ (U i).1.ι)).obj N).Presentation,
        P.IsFinite) := by
  obtain ⟨DM, hDM⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨DN, hDN⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData N
  let := hDM
  let := hDN
  obtain ⟨I, U, hU, hsub⟩ := exists_common_affine_refinement DM.X DN.X
    ((Opens.coversTop_iff X _).mp DM.coversTop)
    ((Opens.coversTop_iff X _).mp DN.coversTop)
  refine ⟨I, U, hU, ?_⟩
  intro k
  obtain ⟨i, j, hi, hj⟩ := hsub k
  let : (DM.presentation i).IsFinite := hDM.isFinite_presentation i
  let : (DN.presentation j).IsFinite := hDN.isFinite_presentation j
  exact ⟨exists_presentation_affine_below M (DM.X i) (DM.presentation i) (U k) hi,
    exists_presentation_affine_below N (DN.X j) (DN.presentation j) (U k) hj⟩

/-- The coherent sheaves on a locally Noetherian scheme are closed under kernels. The proof works on
a common affine cover and descends. -/
lemma coherent_kernel {X : Scheme} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  obtain ⟨I, U, hU, hP⟩ := exists_common_affine_presentations M N
  have hlocal (i : I) : ((kernel f).over (U i).1).IsFinitePresentation := by
    let h := (U i).2.isoSpec.inv ≫ (U i).1.ι
    let F : X.Modules ⥤ (Spec Γ(X, (U i).1)).Modules := restrictFunctor h
    have : F.IsLeftAdjoint := inferInstanceAs (restrictFunctor h).IsLeftAdjoint
    have : PreservesFiniteLimits F := CoherentRestriction.preservesFiniteLimits h
    have : IsNoetherianRing Γ(X, (U i).1) := IsLocallyNoetherian.component_noetherian (U i)
    obtain ⟨PM, hPM⟩ := (hP i).1
    obtain ⟨PN, hPN⟩ := (hP i).2
    let := hPM
    let := hPN
    have hp := exists_presentation_kernel_of_presentations (F.map f) PM PN
    have hp' := exists_presentation_iso (PreservesKernel.iso F f).symm hp
    obtain ⟨P, hfin⟩ := exists_presentation_affine_over (kernel f) (U i) hp'
    let := hfin
    exact CoherentLocality.finitePresentation_of_presentation P
  exact @CoherentLocality.finitePresentation_of_coversTop _ _ _ _ _ _ _ _
    (kernel f) I (fun i => (U i).1) ((Opens.coversTop_iff X _).mpr hU) hlocal

lemma coherent_cokernel {X : Scheme} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  obtain ⟨I, U, hU, hP⟩ := exists_common_affine_presentations M N
  have hlocal (i : I) : ((cokernel f).over (U i).1).IsFinitePresentation := by
    let h := (U i).2.isoSpec.inv ≫ (U i).1.ι
    let F : X.Modules ⥤ (Spec Γ(X, (U i).1)).Modules := restrictFunctor h
    have : F.IsLeftAdjoint := inferInstanceAs (restrictFunctor h).IsLeftAdjoint
    have : IsNoetherianRing Γ(X, (U i).1) := IsLocallyNoetherian.component_noetherian (U i)
    obtain ⟨PM, hPM⟩ := (hP i).1
    obtain ⟨PN, hPN⟩ := (hP i).2
    let := hPM
    let := hPN
    have hp := exists_presentation_cokernel_of_presentations (F.map f) PM PN
    have hp' := exists_presentation_iso (PreservesCokernel.iso F f).symm hp
    obtain ⟨P, hfin⟩ := exists_presentation_affine_over (cokernel f) (U i) hp'
    let := hfin
    exact CoherentLocality.finitePresentation_of_presentation P
  exact @CoherentLocality.finitePresentation_of_coversTop _ _ _ _ _ _ _ _
    (cokernel f) I (fun i => (U i).1) ((Opens.coversTop_iff X _).mpr hU) hlocal
lemma coherent_prod {X : Scheme} [IsLocallyNoetherian X]
    (M N : X.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⨯ N).IsFinitePresentation := by
  obtain ⟨I, U, hU, hP⟩ := exists_common_affine_presentations M N
  have hlocal (i : I) : ((M ⨯ N).over (U i).1).IsFinitePresentation := by
    let h := (U i).2.isoSpec.inv ≫ (U i).1.ι
    let F : X.Modules ⥤ (Spec Γ(X, (U i).1)).Modules := restrictFunctor h
    have : F.IsLeftAdjoint := inferInstanceAs (restrictFunctor h).IsLeftAdjoint
    have : PreservesFiniteLimits F := CoherentRestriction.preservesFiniteLimits h
    have : IsNoetherianRing Γ(X, (U i).1) := IsLocallyNoetherian.component_noetherian (U i)
    obtain ⟨PM, hPM⟩ := (hP i).1
    obtain ⟨PN, hPN⟩ := (hP i).2
    let := hPM
    let := hPN
    have hp := exists_presentation_prod_of_presentations (F.obj M) (F.obj N) PM PN
    have hp' := exists_presentation_iso (PreservesLimitPair.iso F M N).symm hp
    obtain ⟨P, hfin⟩ := exists_presentation_affine_over (M ⨯ N) (U i) hp'
    let := hfin
    exact CoherentLocality.finitePresentation_of_presentation P
  exact @CoherentLocality.finitePresentation_of_coversTop _ _ _ _ _ _ _ _
    (M ⨯ N) I (fun i => (U i).1) ((Opens.coversTop_iff X _).mpr hU) hlocal

instance coherentContainsZero {X : Scheme} [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero := by
  let F : X.Modules := SheafOfModules.free PUnit
  exact ⟨kernel (𝟙 F), isZero_kernel_of_mono _, coherent_kernel_free (𝟙 F)⟩

instance coherentClosedKernels {X : Scheme} [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro Y ⟨f, k, hk, hM, hN⟩
    let := hM
    let := hN
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) (coherent_kernel f)

instance coherentClosedCokernels {X : Scheme} [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro Y ⟨f, k, hk, hM, hN⟩
    let := hM
    let := hN
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) (coherent_cokernel f)

instance coherentClosedBinaryProducts {X : Scheme} [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro Y ⟨F, hF⟩
  let := hF ⟨WalkingPair.left⟩
  let := hF ⟨WalkingPair.right⟩
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (HasLimit.isoOfNatIso (diagramIsoPair F)).symm
    (coherent_prod (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩))

instance coherentClosedFiniteProducts {X : Scheme} [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The abelian category of coherent structure-sheaf modules. -/
abbrev Coh (X : Scheme) :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).FullSubcategory

instance {X : Scheme} [IsLocallyNoetherian X] : Abelian (Coh X) := inferInstance

end CoherentGlobal


end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
lemma coherent_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) [M.IsFinitePresentation] :
    ((restrictFunctor f).obj M).IsFinitePresentation := by
  have (U : X.Opens) : (Over.post (X := U) f.opensFunctor).IsContinuous
      ((Opens.grothendieckTopology X).over U)
      ((Opens.grothendieckTopology Y).over (f ''ᵁ U)) := by
    infer_instance
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf _ _).map φ) := by
    change IsIso (Functor.whiskerRight α (forget₂ CommRingCat RingCat))
    infer_instance
  have hφ : IsIso φ :=
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) RingCat).isIso_of_isIso_map φ
  exact @CoherentLocality.finitePresentation_pushforward_of_isLeftAdjoint
    _ _ _ _ _ _ _ _ _ _ _ _ f.opensFunctor _ _ φ (restrictUnitIso f) _ _ hφ _ _ M _
end CoherentGlobal

namespace CoherentGlobal
open Scheme.Modules
lemma coherent_over_of_restrict {X : Scheme.{0}} (U : X.Opens) (M : X.Modules)
    [((restrictFunctor U.ι).obj M).IsFinitePresentation] :
    (M.over U).IsFinitePresentation := by
  have : ((overEquiv U).inverse.obj ((restrictFunctor U.ι).obj M)).IsFinitePresentation :=
    finitePresentation_overEquiv_inverse U _
  let e : M.over U ≅ (overEquiv U).inverse.obj ((restrictFunctor U.ι).obj M) :=
    (overEquiv U).unitIso.app _ ≪≫
      (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)
  exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso e.symm
    inferInstance

lemma coherent_of_affine_restrict {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, ((restrictFunctor U.1.ι).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have (U : X.affineOpens) : (M.over U.1).IsFinitePresentation := by
    let := h U
    exact coherent_over_of_restrict U.1 M
  exact CoherentLocality.finitePresentation_of_coversTop M (fun U : X.affineOpens => U.1)
    ((Opens.coversTop_iff X _).mpr (iSup_affineOpens_eq_top X))
end CoherentGlobal

end

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat
open scoped _root_.ModuleCat
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
def restrictScalarsAlgebraEquiv :
    ((_root_.ModuleCat.restrictScalars (algebraMap R S)).obj (_root_.ModuleCat.of S S)) ≃ₗ[R] S where
  __ := Equiv.refl S
  map_add' _ _ := rfl
  map_smul' r s := by
    exact (@Algebra.smul_def R S _ _ _ r s).symm

def extendScalarsTensorEquiv (M : ModuleCat R) :
    ((_root_.ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] TensorProduct R S M where
  __ := (TensorProduct.congr (restrictScalarsAlgebraEquiv (R := R) (S := S))
    (LinearEquiv.refl R M)).toAddEquiv
  map_smul' s x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      change ((_root_.ModuleCat.extendScalars (algebraMap R S)).obj M) at x y
      let e : ((_root_.ModuleCat.extendScalars (algebraMap R S)).obj M) ≃+ TensorProduct R S M :=
        (TensorProduct.congr (restrictScalarsAlgebraEquiv (R := R) (S := S))
          (LinearEquiv.refl R M)).toAddEquiv
      change e (s • (x + y)) = s • e (x + y)
      calc
        _ = e (s • x + s • y) := congrArg e (smul_add s x y)
        _ = e (s • x) + e (s • y) := e.map_add _ _
        _ = s • e x + s • e y := congrArg₂ (· + ·) hx hy
        _ = s • (e x + e y) := (smul_add s _ _).symm
        _ = s • e (x + y) := congrArg (s • ·) (e.map_add x y).symm
    | tmul t m =>
      erw [ModuleCat.ExtendScalars.smul_tmul (algebraMap R S)]
      rfl
end ModuleCat

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

lemma finiteGamma_of_presentation {R : CommRingCat.{0}} (M : (Spec R).Modules)
    (P : M.Presentation) [P.IsFinite] : Module.Finite R (moduleSpecΓFunctor.obj M) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_finite_module_of_presentation M P
  let := hN
  let e' : N ≅ moduleSpecΓFunctor.obj M :=
    tilde.toTildeΓNatIso.app N ≪≫ moduleSpecΓFunctor.mapIso e
  exact Module.Finite.equiv e'.toLinearEquiv

lemma exists_presentation_restrict_below {X Y : Scheme.{0}} (M : X.Modules)
    (U : X.Opens) (P : (M.over U).Presentation) [P.IsFinite]
    (f : Y ⟶ U.toScheme) [IsOpenImmersion f] :
    ∃ Q : ((restrictFunctor (f ≫ U.ι)).obj M).Presentation, Q.IsFinite := by
  let F : SheafOfModules (X.ringCatSheaf.over U) ⥤ SheafOfModules Y.ringCatSheaf :=
    (overEquiv U).functor ⋙ restrictFunctor f
  have : F.IsLeftAdjoint := inferInstanceAs
    ((overEquiv U).functor ⋙ restrictFunctor f).IsLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  let e : SheafOfModules.unit Y.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (restrictUnitIso f).symm ≪≫ (restrictFunctor f).mapIso
      (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm
  let q : F.obj (M.over U) ≅ (restrictFunctor (f ≫ U.ι)).obj M :=
    (restrictFunctor f).mapIso ((overFunctorEquiv U).app M) ≪≫
      ((restrictFunctorComp f U.ι).app M).symm
  exact exists_presentation_iso q ⟨P.map F e, inferInstance⟩

lemma exists_presentation_basicOpen_below {R : CommRingCat.{0}} (M : (Spec R).Modules)
    (U : (Spec R).Opens) (P : (M.over U).Presentation) [P.IsFinite]
    (g : R) (hg : PrimeSpectrum.basicOpen g ≤ U) :
    let f : R ⟶ CommRingCat.of (Localization.Away g) := CommRingCat.ofHom (algebraMap _ _)
    ∃ Q : ((restrictFunctor (Spec.map f)).obj M).Presentation, Q.IsFinite := by
  dsimp only
  let t := (Spec R).homOfLE hg
  let h := (basicOpenIsoSpecAway g).inv ≫ t
  have : IsOpenImmersion t :=
    AlgebraicGeometry.instIsOpenImmersionHomOfLE (Spec R) hg
  have : IsOpenImmersion h := IsOpenImmersion.comp _ _
  obtain ⟨Q, hQ⟩ := exists_presentation_restrict_below M U P h
  let := hQ
  have he : h ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) := by
    let e := basicOpenIsoSpecAway g
    calc
      _ = e.inv ≫ (t ≫ U.ι) := Category.assoc _ _ _
      _ = e.inv ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) :=
        congrArg (e.inv ≫ ·) ((Spec R).homOfLE_ι hg)
      _ = e.inv ≫ (e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away g)))) :=
        congrArg (e.inv ≫ ·) (basicOpenIsoSpecAway_hom_SpecMap g).symm
      _ = _ := (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away g)))) e.inv_hom_id).trans (Category.id_comp _))
  let e := (restrictFunctorCongr he).app M
  exact exists_presentation_iso e ⟨Q, inferInstance⟩

end CoherentGlobal

namespace CoherentGlobal
open Scheme.Modules
/-- Affine pullback on a quasicoherent sheaf, on global sections. -/
def affinePullbackGammaIso {R S : CommRingCat.{0}} (f : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map f)).obj M) ≅
      (ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj M) :=
  moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullback (Spec.map f)).mapIso (asIso (Scheme.Modules.fromTildeΓ M)).symm ≪≫
      (AffinePullback.pullbackTildeIso f).app _) ≪≫
    (tilde.toTildeΓNatIso.app _).symm

lemma finite_extendScalarsGamma_of_restrict_presentation {R S : CommRingCat.{0}}
    (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (P : ((restrictFunctor (Spec.map f)).obj M).Presentation) [P.IsFinite] :
    Module.Finite S ((ModuleCat.extendScalars f.hom).obj (moduleSpecΓFunctor.obj M)) := by
  have : Module.Finite S
      (moduleSpecΓFunctor.obj ((restrictFunctor (Spec.map f)).obj M)) :=
    finiteGamma_of_presentation _ P
  let e := moduleSpecΓFunctor.mapIso ((restrictFunctorIsoPullback (Spec.map f)).app M) ≪≫
    affinePullbackGammaIso f M
  exact Module.Finite.equiv e.toLinearEquiv

lemma finite_localizedModule_of_extendScalars {R : CommRingCat.{0}} (M : ModuleCat R)
    (g : R) [Module.Finite (Localization.Away g)
      ((ModuleCat.extendScalars (algebraMap R (Localization.Away g))).obj M)] :
    Module.Finite (Localization.Away g) (LocalizedModule.Away g M) :=
  by
  have : Module.Finite (Localization.Away g) (TensorProduct R (Localization.Away g) M) :=
    Module.Finite.equiv (ModuleCat.extendScalarsTensorEquiv M)
  exact Module.Finite.equiv (LocalizedModule.equivTensorProduct (Submonoid.powers g) M).symm

lemma finite_localizedGamma_of_basicOpen_presentation {R : CommRingCat.{0}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (g : R)
    (P : ((restrictFunctor (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away g))))).obj M).Presentation) [P.IsFinite] :
    Module.Finite (Localization.Away g)
      (LocalizedModule.Away g (moduleSpecΓFunctor.obj M)) := by
  let f : R ⟶ CommRingCat.of (Localization.Away g) := CommRingCat.ofHom (algebraMap _ _)
  let := finite_extendScalarsGamma_of_restrict_presentation f M P
  exact finite_localizedModule_of_extendScalars (moduleSpecΓFunctor.obj M) g

/-- A basis of principal opens subordinate to any open cover spans the unit ideal. -/
lemma basicOpen_refinement_span {R : CommRingCat.{0}} {I : Type}
    (U : I → (Spec R).Opens) (hU : (⨆ i, U i) = ⊤) :
    Ideal.span {g : R | ∃ i, PrimeSpectrum.basicOpen g ≤ U i} = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hi (U i).isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨g,
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hg⟩, hxg⟩⟩

/-- Every coherent sheaf on an affine scheme has a finite module of sections. Finiteness is
descended from its finite local presentations, not assumed from an abstract equivalence with
finite modules. -/
lemma finiteGamma_of_coherent {R : CommRingCat.{0}} (M : (Spec R).Modules)
    [M.IsFinitePresentation] : Module.Finite R (moduleSpecΓFunctor.obj M) := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  obtain ⟨D, hD⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let := hD
  let s : Set R := {g | ∃ i, PrimeSpectrum.basicOpen g ≤ D.X i}
  have hs : Ideal.span s = ⊤ := basicOpen_refinement_span D.X
    ((Opens.coversTop_iff (Spec R) _).mp D.coversTop)
  apply Module.Finite.of_localizationSpan s hs
  intro g
  obtain ⟨i, hi⟩ := g.property
  let : (D.presentation i).IsFinite := hD.isFinite_presentation i
  obtain ⟨P, hP⟩ := exists_presentation_basicOpen_below M (D.X i) (D.presentation i) g hi
  let := hP
  exact finite_localizedGamma_of_basicOpen_presentation M g P
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
lemma finite_restrictScalars {A B : CommRingCat.{0}} (f : A ⟶ B) (hf : f.hom.Finite)
    (M : ModuleCat B) [Module.Finite B M] :
    Module.Finite A ((ModuleCat.restrictScalars f.hom).obj M) := by
  let := f.hom.toAlgebra
  have : Module.Finite A B := hf
  have : IsScalarTower A B ((ModuleCat.restrictScalars f.hom).obj M) :=
    IsScalarTower.restrictScalars A B M
  have : Module.Finite B ((ModuleCat.restrictScalars f.hom).obj M) :=
    inferInstanceAs (Module.Finite B M)
  exact Module.Finite.trans B ((ModuleCat.restrictScalars f.hom).obj M)

/-- Finite pushforward of a coherent sheaf on an affine scheme is coherent, proved from its affine
module of sections. -/
lemma coherent_affinePushforward {A B : CommRingCat.{0}} [IsNoetherianRing A]
    (f : A ⟶ B) (hf : f.hom.Finite) (M : (Spec B).Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward (Spec.map f)).obj M).IsFinitePresentation := by
  let := finiteGamma_of_coherent M
  let := finite_restrictScalars f hf (moduleSpecΓFunctor.obj M)
  let N := (ModuleCat.restrictScalars f.hom).obj (moduleSpecΓFunctor.obj M)
  obtain ⟨P, hP⟩ := exists_presentation_tilde N
  let := hP
  have hN : (tilde N).IsFinitePresentation :=
    CoherentLocality.finitePresentation_of_presentation P
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have : IsIso (Scheme.Modules.fromTildeΓ M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let e := (Scheme.Modules.pushforward (Spec.map f)).mapIso
      (asIso (Scheme.Modules.fromTildeΓ M)).symm ≪≫
    AffinePullback.pushforwardTildeIso f (moduleSpecΓFunctor.obj M)
  exact (SheafOfModules.isFinitePresentation (Spec A).ringCatSheaf).prop_of_iso e.symm hN
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
/-- Pushforward under a scheme isomorphism is restriction along its inverse. -/
def pushforwardIsoRestrict {X Y : Scheme.{0}} (e : X ≅ Y) :
    pushforward e.hom ≅ restrictFunctor e.inv := by
  let a : restrictFunctor e.hom ⋙ restrictFunctor e.inv ≅ 𝟭 Y.Modules :=
    (restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr e.inv_hom_id ≪≫ restrictFunctorId
  exact (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (pushforward e.hom) a.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictFunctorAdjCounitIso e.hom) (restrictFunctor e.inv) ≪≫
    Functor.leftUnitor _

lemma coherent_pushforward_iso {X Y : Scheme.{0}} (e : X ≅ Y)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward e.hom).obj M).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrict e).app M).symm (coherent_restrict e.inv M)

/-- Affine charts, without assuming that the affine schemes are definitionally Spec. -/
lemma coherent_pushforward_affine {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  have : IsNoetherianRing Γ(Y, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : ((pushforward X.isoSpec.hom).obj M).IsFinitePresentation :=
    coherent_pushforward_iso X.isoSpec M
  have : ((pushforward (Spec.map f.appTop)).obj
      ((pushforward X.isoSpec.hom).obj M)).IsFinitePresentation :=
    coherent_affinePushforward f.appTop f.finite_appTop _
  have hM : ((pushforward Y.isoSpec.inv).obj
      ((pushforward (Spec.map f.appTop)).obj
        ((pushforward X.isoSpec.hom).obj M))).IsFinitePresentation :=
    coherent_pushforward_iso Y.isoSpec.symm _
  have he : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  let e := (pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app
      ((pushforward X.isoSpec.hom).obj M) ≪≫
    (pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app M ≪≫
    (pushforwardCongr he).app M
  exact (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e hM
/-- Finite pushforward preserves the coherent category. -/
lemma coherent_pushforward {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsFinitePresentation] :
    ((pushforward f).obj M).IsFinitePresentation := by
  apply coherent_of_affine_restrict
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsFinite (f ∣_ U.1) := inferInstance
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have : ((restrictFunctor (f ⁻¹ᵁ U.1).ι).obj M).IsFinitePresentation :=
    coherent_restrict _ _
  have hN := coherent_pushforward_affine (f ∣_ U.1)
    ((restrictFunctor (f ⁻¹ᵁ U.1).ι).obj M)
  exact (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso
    (CoherentBaseChange.pushforwardRestrictIso f U.1 M).symm hN
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

instance affineGamma_additive {R : CommRingCat.{0}} :
    (show (Spec R).Modules ⥤ ModuleCat R from moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl

/-- The affine module/sheaf comparison respects short complexes. -/
def shortComplexTildeIso {R : CommRingCat.{0}} (S : ShortComplex (Spec R).Modules)
    [IsIso (fromTildeΓ S.X₁)] [IsIso (fromTildeΓ S.X₂)] [IsIso (fromTildeΓ S.X₃)] :
    (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ≅ S :=
  ShortComplex.isoMk
    (@asIso _ _ _ _ (fromTildeΓ S.X₁) (inferInstanceAs (IsIso (fromTildeΓ S.X₁))))
    (@asIso _ _ _ _ (fromTildeΓ S.X₂) (inferInstanceAs (IsIso (fromTildeΓ S.X₂))))
    (@asIso _ _ _ _ (fromTildeΓ S.X₃) (inferInstanceAs (IsIso (fromTildeΓ S.X₃))))
    (fromTildeΓNatTrans.naturality S.f).symm
    (fromTildeΓNatTrans.naturality S.g).symm

lemma exact_iff_affineGamma {R : CommRingCat.{0}} (S : ShortComplex (Spec R).Modules)
    [IsIso (fromTildeΓ S.X₁)] [IsIso (fromTildeΓ S.X₂)] [IsIso (fromTildeΓ S.X₃)] :
    S.Exact ↔ (S.map (moduleSpecΓFunctor (R := R))).Exact := by
  rw [← ShortComplex.exact_iff_of_iso (shortComplexTildeIso S)]
  exact (S.map (moduleSpecΓFunctor (R := R))).exact_map_iff_of_faithful (tilde.functor R)

/-- Affine pushforward is exact on the quasicoherent sheaves; there is no claim that arbitrary sheaf
pushforward is exact. -/
lemma exact_affinePushforward {A B : CommRingCat.{0}} (f : A ⟶ B)
    (S : ShortComplex (Spec B).Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.Exact) : (S.map (pushforward (Spec.map f))).Exact := by
  have : IsIso (fromTildeΓ ((pushforward (Spec.map f)).obj S.X₁)) :=
    isIso_fromTildeΓ_pushforward f S.X₁
  have : IsIso (fromTildeΓ ((pushforward (Spec.map f)).obj S.X₂)) :=
    isIso_fromTildeΓ_pushforward f S.X₂
  have : IsIso (fromTildeΓ ((pushforward (Spec.map f)).obj S.X₃)) :=
    isIso_fromTildeΓ_pushforward f S.X₃
  have : IsIso (fromTildeΓ (S.map (pushforward (Spec.map f))).X₁) :=
    isIso_fromTildeΓ_pushforward f S.X₁
  have : IsIso (fromTildeΓ (S.map (pushforward (Spec.map f))).X₂) :=
    isIso_fromTildeΓ_pushforward f S.X₂
  have : IsIso (fromTildeΓ (S.map (pushforward (Spec.map f))).X₃) :=
    isIso_fromTildeΓ_pushforward f S.X₃
  apply (exact_iff_affineGamma (S.map (pushforward (Spec.map f)))).mpr
  exact ShortComplex.exact_of_iso (S.mapNatIso (AffinePullback.pushforwardGammaIso f).symm)
    (((exact_iff_affineGamma S).mp hS).map (ModuleCat.restrictScalars f.hom))

end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

/-- Affine opens below a fixed open form an open cover of that open. -/
lemma affine_below_cover {X : Scheme.{0}} (U : X.Opens) :
    U ≤ ⨆ V : {V : X.affineOpens // V.1 ≤ U}, V.1.1 := by
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩

lemma hom_ext_affine {X : Scheme.{0}} {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ U : X.affineOpens, (restrictFunctor U.1.ι).map f =
      (restrictFunctor U.1.ι).map g) : f = g := by
  have hApp (U : X.affineOpens) : f.app U.1 = g.app U.1 := by
    have hh := congrArg (fun z => z.app ⊤) (h U)
    change f.app (U.1.ι ''ᵁ ⊤) = g.app (U.1.ι ''ᵁ ⊤) at hh
    have hh' : f.mapPresheaf.app (op (U.1.ι ''ᵁ ⊤)) =
        g.mapPresheaf.app (op (U.1.ι ''ᵁ ⊤)) := hh
    rw [U.1.ι_image_top] at hh'
    exact hh'
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro x
  let V : {V : X.affineOpens // V.1 ≤ U} → X.Opens := fun V => V.1.1
  let Q : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf X.ringCatSheaf).obj N
  apply Q.eq_of_locally_eq' V U (fun V => homOfLE V.2) (affine_below_cover U)
  intro W
  have hf := f.mapPresheaf.naturality (homOfLE W.2).op
  have hg := g.mapPresheaf.naturality (homOfLE W.2).op
  change N.presheaf.map (homOfLE W.2).op (f.app U x) =
    N.presheaf.map (homOfLE W.2).op (g.app U x)
  simp only [mapPresheaf_app] at hf hg
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← hf, ← hg,
    hApp W.1]

lemma isZero_of_affine_restrict {X : Scheme.{0}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, IsZero ((restrictFunctor U.1.ι).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply hom_ext_affine
  intro U
  exact (h U).eq_of_src _ _

/-- Exactness of module sheaves is local on affine opens. -/
lemma exact_of_affine_restrict {X : Scheme.{0}} (S : ShortComplex X.Modules)
    (h : ∀ U : X.affineOpens, (S.map (restrictFunctor U.1.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply isZero_of_affine_restrict
  intro U
  have : PreservesFiniteLimits (restrictFunctor U.1.ι) :=
    CoherentRestriction.preservesFiniteLimits U.1.ι
  exact ((S.map (restrictFunctor U.1.ι)).exact_iff_isZero_homology.mp (h U)).of_iso
    (ShortComplex.mapHomologyIso S (restrictFunctor U.1.ι)).symm
end CoherentGlobal

end

end OAI

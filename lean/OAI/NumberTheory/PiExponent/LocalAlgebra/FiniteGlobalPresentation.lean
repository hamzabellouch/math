import OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite
import OAI.NumberTheory.PiExponent.Approximation.TwistSections
import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

section PresentationMap
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

instance presentation_map_isFinite (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u,u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    rw [SheafOfModules.Presentation.map_generators_I]
    infer_instance⟩
  isFiniteType_relations := ⟨by
    rw [SheafOfModules.Presentation.map_relations_I]
    infer_instance⟩
private def presentationOfIso {N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end PresentationMap

theorem isFinitePresentation_of_presentation {X : Scheme.{u}} {M : X.Modules}
    (P : M.Presentation) [hP : P.IsFinite] : M.IsFinitePresentation := by
  let q := P.quasicoherentData
  have : q.IsFinitePresentation := by
    constructor
    intro U
    exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem tilde_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (N : ModuleCat R) [Module.Finite R N] :
    ∃ P : (tilde N).Presentation, P.IsFinite := by
  classical
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := R) (M := N)
  let K := LinearMap.ker (Finsupp.linearCombination (M := N) R ((↑) : s → N))
  obtain ⟨t,ht⟩ := IsNoetherian.noetherian K
  let P := presentationTilde N (s : Set N) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite s
      infer_instance
    · constructor
      change Finite t
      infer_instance
  exact ⟨P,inferInstance⟩

theorem tilde_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (N : ModuleCat R) [Module.Finite R N] : (tilde N).IsFinitePresentation := by
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation N
  exact isFinitePresentation_of_presentation P

theorem spec_kernel_isQuasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  let g := (tilde.functor R).preimage
    (em.hom ≫ f ≫ en.inv)
  let e : (tilde.functor R).obj (kernel g) ≅ kernel f :=
    PreservesKernel.iso (tilde.functor R) g ≪≫
      kernel.mapIso ((tilde.functor R).map g) f em
        en (by
          change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
          erw [Functor.map_preimage]
          exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
            (congrArg (fun q => em.hom ≫ q)
              ((Category.assoc f en.inv en.hom).trans
                ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (inferInstanceAs (tilde (kernel g)).IsQuasicoherent)

theorem spec_exists_finitePresentation_of_sections {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ P : M.Presentation, P.IsFinite := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation
    ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))
  let h := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨presentationOfIso (@asIso _ _ _ _ M.fromTildeΓ h) P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem spec_kernel_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] (f : M ⟶ N) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  have := spec_kernel_isQuasicoherent f
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    inferInstanceAs (Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)))
  let g := moduleSpecΓFunctor.map (kernel.ι f)
  have : Mono g := inferInstanceAs (Mono (moduleSpecΓFunctor.map (kernel.ι f)))
  have : Module.Finite R ((modulesSpecToSheaf.obj (kernel f)).obj.obj (op ⊤)) :=
    Module.Finite.of_injective g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
  exact spec_exists_finitePresentation_of_sections (kernel f)

def presentationOver_of_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (Sheaf.over X.ringCatSheaf U) := E.inverse
  let : PreservesColimitsOfSize.{u,u} F :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  let : IsIso e.hom := e.isIso_hom
  exact presentationOfIso e (P.map F (E.unitIso.app _))

instance presentationOver_of_restrict_isFinite {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    (presentationOver_of_restrict M U P).IsFinite := by
  exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

theorem isFinitePresentation_of_affine_presentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, ∃ P : (M.restrict U.1.ι).Presentation, P.IsFinite) :
    M.IsFinitePresentation := by
  classical
  let pres (U : X.affineOpens) := (h U).choose
  have hpres (U : X.affineOpens) : (pres U).IsFinite := (h U).choose_spec
  let q : M.QuasicoherentData := {
    I := X.affineOpens
    X U := U.1
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hx
      obtain ⟨U,hU,hxU,hUt⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Opens.mem_iSup.mpr ⟨⟨U,hU⟩,hxU⟩
    presentation U := presentationOver_of_restrict M U.1 (pres U) }
  have : q.IsFinitePresentation := by
    constructor
    intro U
    change (presentationOver_of_restrict M U.1 (pres U)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem affine_kernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hM : LocallyFinitelyGenerated M) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (M.restrict a) (hM.restrict a)
  obtain ⟨P,hP⟩ := spec_kernel_exists_finitePresentation (F.map f)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  let P' := presentationOfIso e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (kernel f)
  have e₂ : (kernel f).restrict (𝟙 X) ≅ ((kernel f).restrict a).restrict b := by
    change (kernel f).restrict (b ≫ a) ≅ ((kernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (kernel f)
  let : IsIso e₃.hom := e₃.isIso_hom
  exact ⟨presentationOfIso e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem free_isFinitePresentation (X : Scheme.{u}) (I : Type u) [Finite I] :
    (SheafOfModules.free (R := X.ringCatSheaf) I).IsFinitePresentation := by
  let f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty) ⟶
      SheafOfModules.free I := 0
  let P := SheafOfModules.presentationOfIsCokernelFree f (𝟙 _) (by simp [f])
    (CokernelCofork.IsColimit.ofId f rfl)
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite I
      infer_instance
    · constructor
      change Finite (ULift.{u} Empty)
      infer_instance
  exact isFinitePresentation_of_presentation P

theorem kernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_kernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.1.ι)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem kernel_generators_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    (kernel s.π).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := free_isFinitePresentation X s.I
  exact kernel_isFinitePresentation s.π

theorem exists_local_finitePresentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ P : (M.restrict U.ι).Presentation, P.IsFinite := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let : (q.presentation i).IsFinite := hq.isFinite_presentation i
  let P := (q.presentation i).map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  let : IsIso e.hom := e.isIso_hom
  exact ⟨q.X i, hi, presentationOfIso e P,
    ⟨⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩,
      ⟨(hq.isFinite_presentation i).isFiniteType_relations.finite⟩⟩⟩

theorem isFinitePresentation_of_localPresentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ P : (M.restrict U.ι).Presentation, P.IsFinite) : M.IsFinitePresentation := by
  classical
  choose U hx P hP using h
  have hP' (x : X) : (P x).IsFinite := hP x
  let q : M.QuasicoherentData := {
    I := X
    X := U
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hxtop
      exact Opens.mem_iSup.mpr ⟨x,hx x⟩
    presentation x := presentationOver_of_restrict M (U x) (P x) }
  have : q.IsFinitePresentation := by
    constructor
    intro x
    change (presentationOver_of_restrict M (U x) (P x)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem finitePresentation_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    ∃ Q : (M.restrict V.ι).Presentation, Q.IsFinite := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let Q := P.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

def restrictIsoOfLE {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict V.ι ≅ N.restrict V.ι := by
  let e' := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app N).symm
  simp only [X.homOfLE_ι h] at e'
  exact e'

theorem isFinitePresentation_of_locally_iso {X : Scheme.{u}} (M N : X.Modules)
    [M.IsFinitePresentation]
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ Nonempty (N.restrict V.ι ≅ M.restrict V.ι)) :
    N.IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro x
  obtain ⟨V,hxV,⟨e⟩⟩ := h x
  obtain ⟨U,hxU,P,hP⟩ := exists_local_finitePresentation M x
  obtain ⟨Q,hQ⟩ := finitePresentation_of_le M (V := U ⊓ V) inf_le_left P
  let e' := restrictIsoOfLE (V := U ⊓ V) inf_le_right e
  let : IsIso e'.inv := e'.isIso_inv
  exact ⟨U ⊓ V, ⟨hxU,hxV⟩, presentationOfIso e'.symm Q,
    ⟨⟨hQ.isFiniteType_generators.finite⟩, ⟨hQ.isFiniteType_relations.finite⟩⟩⟩

theorem moduleTwist_isFinitePresentation {X : Scheme.{0}}
    (L : PiExponentSeshadri.Geometry.LineBundle X) (n : ℕ) (M : X.Modules)
    [M.IsFinitePresentation] :
    ((PiExponentSeshadri.Geometry.moduleTwistFunctor L n).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_locally_iso M
  intro x
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U,hxU,⟨(PiExponentSeshadri.Geometry.moduleTwistRestrictFrame L U e n).app M⟩⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI

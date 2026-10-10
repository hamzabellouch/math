import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Geometry.SupportedSheaf

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def openSectionModule (M : X.Modules) (U : X.Opens) : ModuleCat Γ(X,⊤) := by
  letI := Module.compHom Γ(M,U) (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  exact ModuleCat.of Γ(X,⊤) Γ(M,U)

def openSectionRestriction (M : X.Modules) (U : X.Opens) :
    Γ(M,⊤) →ₗ[Γ(X,⊤)] openSectionModule M U where
  toFun := M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  map_add' := map_add _
  map_smul' := fun r s => M.map_smul _ r s

def disjointSupportCoverEquiv (M : X.Modules) {ι : Type*} (D : ι → X.Opens)
    (hcover : ⊤ ≤ ⨆ i, D i)
    (hz : ∀ i j, i ≠ j → Subsingleton Γ(M,D i ⊓ D j)) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] ((i : ι) → openSectionModule M (D i)) := by
  let F : (X : TopCat).Sheaf AddCommGrpCat :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let f := LinearMap.pi (fun i => openSectionRestriction M (D i))
  apply LinearEquiv.ofBijective f
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' D ⊤ (fun _ => homOfLE le_top) hcover s t
    intro i
    exact congrFun h i
  · intro s
    have hc : TopCat.Presheaf.IsCompatible F.obj D s := by
      intro i j
      by_cases h : i = j
      · subst j; rfl
      · let : Subsingleton (F.obj.obj (op (D i ⊓ D j))) := hz i j h
        exact Subsingleton.elim _ _
    obtain ⟨t,ht,_⟩ := F.existsUnique_gluing' D ⊤ (fun _ => homOfLE le_top) hcover s hc
    exact ⟨t,funext ht⟩

def openSectionIso (M N : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    openSectionModule M U ≃ₗ[Γ(X,⊤)] openSectionModule N U := by
  let etop := ((Scheme.Modules.toPresheaf U.toScheme).mapIso e).app (op ⊤)
  let a := (M.restrictAppIso U.ι ⊤).symm ≪≫ etop ≪≫ N.restrictAppIso U.ι ⊤
  have E : openSectionModule M (U.ι ''ᵁ ⊤) ≃ₗ[Γ(X,⊤)]
      openSectionModule N (U.ι ''ᵁ ⊤) := by
    refine { toFun := fun x => a.hom x
             invFun := fun x => a.inv x
             left_inv := by intro s; exact ConcreteCategory.congr_hom a.hom_inv_id s
             right_inv := by intro s; exact ConcreteCategory.congr_hom a.inv_hom_id s
             map_add' := map_add _
             map_smul' := ?_ }
    intro r s
    change Γ(M,U.ι ''ᵁ ⊤) at s
    change (N.restrictAppIso U.ι ⊤).hom
        (e.hom.app ⊤ ((M.restrictAppIso U.ι ⊤).inv
          ((X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) • s))) =
      (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) • a.hom s
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply,e.hom.app_smul,
      Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
  exact htop ▸ E

def finiteSupportLocallyIsoGlobal (M N : X.Modules) (S : Set X)
    (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hM : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x))
    (hN : ∀ x ∉ S, Subsingleton (N.presheaf.stalk x))
    (hloc : ∀ x ∈ S, ∃ U : X.Opens, x ∈ U ∧ Nonempty (M.restrict U.ι ≅ N.restrict U.ι)) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) := by
  classical
  choose U hx he using fun x : S => hloc x x.property
  let e : ∀ x : S, M.restrict (U x).ι ≅ N.restrict (U x).ι := fun x => (he x).some
  have hc : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hfin.isClosed_biUnion hclosed
  have hcx (x : S) : IsClosed (S \ {x.val}) := by
    rw [← Set.biUnion_of_singleton (S \ {x.val})]
    exact (hfin.subset Set.sdiff_subset).isClosed_biUnion (fun y hy => hclosed y hy.1)
  let V : S → X.Opens := fun x => U x ⊓ ⟨(S \ {x.val})ᶜ,(hcx x).isOpen_compl⟩
  let D : Option S → X.Opens := fun x => match x with
    | none => ⟨Sᶜ,hc.isOpen_compl⟩
    | some x => V x
  have hV (x : S) : x.val ∈ V x := ⟨hx x,fun h => h.2 rfl⟩
  have hcover : ⊤ ≤ ⨆ i, D i := by
    intro x _
    by_cases hs : x ∈ S
    · exact Opens.mem_iSup.mpr ⟨some ⟨x,hs⟩,hV ⟨x,hs⟩⟩
    · exact Opens.mem_iSup.mpr ⟨none,hs⟩
  have honly (x : X) (hs : x ∈ S) (i : Option S) (hi : x ∈ D i) :
      i = some ⟨x,hs⟩ := by
    cases i with
    | none => exact (hi hs).elim
    | some y =>
      congr 1
      apply Subtype.ext
      by_contra hne
      exact hi.2 ⟨hs,fun h => hne h.symm⟩
  have hz (P : X.Modules) (hP : ∀ x ∉ S, Subsingleton (P.presheaf.stalk x)) :
      ∀ i j, i ≠ j → Subsingleton Γ(P,D i ⊓ D j) := by
    intro i j hij
    apply FiniteSupport.sections_subsingleton_of_stalks
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj P)
    intro x hx
    apply hP
    intro hs
    exact hij ((honly x hs i hx.1).trans (honly x hs j hx.2).symm)
  have eD (i : Option S) : openSectionModule M (D i) ≃ₗ[Γ(X,⊤)] openSectionModule N (D i) := by
    cases i with
    | none =>
      letI : Subsingleton (openSectionModule M (D none)) := by
        change Subsingleton Γ(M,D none)
        exact FiniteSupport.sections_subsingleton_of_stalks
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) _ (fun x hx => hM x hx)
      letI : Subsingleton (openSectionModule N (D none)) := by
        change Subsingleton Γ(N,D none)
        exact FiniteSupport.sections_subsingleton_of_stalks
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) _ (fun x hx => hN x hx)
      exact LinearEquiv.ofSubsingleton _ _
    | some x =>
      let hVu : V x ≤ U x := inf_le_left
      let nest (P : X.Modules) : (P.restrict (U x).ι).restrict (X.homOfLE hVu) ≅ P.restrict (V x).ι :=
        ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVu) (U x).ι).app P).symm ≪≫
          (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVu)).app P
      exact openSectionIso M N (V x) ((nest M).symm ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hVu)).mapIso (e x) ≪≫ nest N)
  exact (disjointSupportCoverEquiv M D hcover (hz M hM)).trans
    ((LinearEquiv.piCongrRight eD).trans (disjointSupportCoverEquiv N D hcover (hz N hN)).symm)

end
end PiExponentSeshadri.Geometry

end OAI

import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.TensorCurveEuler

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

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

def tensorCokernelLocalIso (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (cokernel (sectionMultiply L M s)).restrict U.ι ≅ (cokernel s).restrict U.ι := by
  let t : M.sheaf.restrict U.ι ⟶ (L.tensor M).sheaf.restrict U.ι :=
    (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiply L M s)
  let twist : O U.toScheme ≅ O U.toScheme := tensorUnitTwist M U f
  let frame : (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
    tensorFrame L M U e f
  let p := f ≪≫ twist
  let q := frame ≪≫ e.symm
  have framed : f.inv ≫ t ≫ frame.hom =
      twist.hom ≫ restrictSection U.ι s ≫ e.hom :=
    tensor_multiply_framed L M s U e f
  have he : t ≫ q.hom = p.hom ≫ restrictSection U.ι s := by
    apply (cancel_epi f.inv).mp
    apply (cancel_mono e.hom).mp
    simpa only [p,q,Iso.trans_hom,Iso.symm_hom,Category.assoc,
      Iso.inv_hom_id_assoc,Iso.hom_inv_id_assoc,Iso.inv_hom_id,Category.comp_id] using framed
  exact PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.ι) _ ≪≫
    cokernel.mapIso t (restrictSection U.ι s) p q he ≪≫
      (restrictCokernelIso s U.ι).symm

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

lemma LineBundle.sectionSupport_closed_points [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) (x : X) (hx : x ∉ isoOpen s) :
    IsClosed ({x} : Set X) := by
  let S : Set X := (isoOpen s : Set X)ᶜ
  have hc : closure ({x} : Set X) ⊆ S :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) (isoOpen s).isOpen.isClosed_compl
  have hsub : (closure ({x} : Set X)).Subsingleton := by
    apply proper_irreducible_closed_subsingleton hd isClosed_closure
      isIrreducible_singleton.closure
    intro he
    have hb : S = Set.univ := Set.eq_univ_of_univ_subset (he ▸ hc)
    exact L.isoOpen_ne_bot s hs (SetLike.coe_injective (by simpa [S] using hb))
  have he : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hsub hy (subset_closure (Set.mem_singleton x))
    · exact subset_closure
  exact he ▸ isClosed_closure

def tensorCokernelGlobalEquiv [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) :
    Γ(cokernel (sectionMultiply L M s),⊤) ≃ₗ[Γ(X,⊤)] Γ(cokernel s,⊤) := by
  classical
  apply finiteSupportLocallyIsoGlobal _ _ (isoOpen s : Set X)ᶜ
    (L.cokernel_support_finite hd s hs) (L.sectionSupport_closed_points hd s hs)
  · intro x hx
    apply cokernel_stalk_subsingleton (sectionMultiply L M s) x
    rw [tensor_multiply_isoOpen]
    exact not_not.mp hx
  · intro x hx
    exact cokernel_stalk_subsingleton s x (not_not.mp hx)
  · intro x _
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    exact ⟨U.1,hx,⟨tensorCokernelLocalIso L M s U.1 e f⟩⟩

end
end MaximalSeshadri.Geometry

end


end
end

end OAI

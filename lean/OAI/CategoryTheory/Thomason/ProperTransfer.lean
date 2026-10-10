import Mathlib
import OAI.CategoryTheory.Thomason.AttachmentComparison
import OAI.CategoryTheory.Thomason.GlobularGeneration
import OAI.CategoryTheory.Thomason.ModelTransfer

namespace OAI

/-! Proper Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open BoundaryProperness (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

abbrev arrow (G : SSet.{u} ⥤ C) (d : PosetAttachment.{u}) := Arrow.mk (inc G d.A)

def Admissible (G : SSet.{u} ⥤ C) : MorphismProperty (C) :=
  fun _ _ f => ∃ d : PosetAttachment.{u}, Nonempty (arrow G d ≅ Arrow.mk f)

instance : (Admissible G).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    rintro _ _ e ⟨d,⟨a⟩⟩
    exact ⟨d,⟨a ≪≫ e⟩⟩)

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma boundary_admissible : boundaryImages (L G) ≤ Admissible G := by
  rintro X Y f ⟨m⟩
  let d : PosetAttachment := {
    B := NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+1))))
    order := inferInstance
    A := oldSet (simplexFaces (SSet.boundary m))
    lower := oldSet_lower _
    retraction := flagRetraction _
    retract := flagRetraction_retract _
    adjunction := flagRetraction_adjunction _ }
  refine ⟨d, ⟨(Arrow.isoMk (G.mapIso (oldFlagsIso (SSet.boundary m)))
    (G.mapIso (Subdivision.sdTwiceSimplexIso m)) ?_).symm⟩⟩
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg G.map (oldFlagsIso_naturality (SSet.boundary m)).symm

section Coproducts
variable {I : Type u} (d : I → PosetAttachment.{u})

def posetCoprodIso (P : I → Type u) [∀ i, PartialOrder (P i)] :
    (∐ fun i => posetObj G (P i)) ≅ posetObj G (Σ i, P i) :=
  (PreservesCoproduct.iso G (fun i => nerve (P i))).symm ≪≫
    G.mapIso (DependentPosets.iso P)

def oldCoprodIso : (∐ fun i => posetObj G (d i).A) ≅ posetObj G (sumData d).A :=
  (PreservesCoproduct.iso G (fun i => nerve (d i).A)).symm ≪≫
    G.mapIso (DependentPosets.oldNerveIso (fun i => (d i).A))

@[reassoc] lemma posetCoprodIso_ι (P : I → Type u) [∀ i, PartialOrder (P i)] (i : I) :
    Sigma.ι (fun i => posetObj G (P i)) i ≫ (posetCoprodIso (G := G) P).hom =
      G.map (nerveMap (DependentPosets.incl P i).toFunctor) := by
  simp only [posetCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.iso_hom_ι]

@[reassoc] lemma oldCoprodIso_ι (i : I) :
    Sigma.ι (fun i => posetObj G (d i).A) i ≫ (oldCoprodIso (G := G) d).hom =
      G.map (nerveMap
        ((DependentPosets.oldIso (fun i => (d i).A)).toOrderEmbedding.toOrderHom.comp
          (DependentPosets.incl (fun i => (d i).A) i)).toFunctor) := by
  simp only [oldCoprodIso, Iso.trans_hom, Iso.symm_hom]
  erw [Functor.mapIso_hom, ← Category.assoc, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.oldNerveIso_ι]
  rfl

lemma coprod_inc : Limits.Sigma.map (fun i => inc G (d i).A) ≫
    (posetCoprodIso (G := G) (fun i => (d i).B)).hom =
    (oldCoprodIso (G := G) d).hom ≫ inc G (sumData d).A := by
  apply Sigma.hom_ext
  intro i
  erw [Sigma.ι_map_assoc, posetCoprodIso_ι]
  erw [← Category.assoc]
  erw [oldCoprodIso_ι]
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Coproducts

instance admissible_coproducts (I : Type u) : (Admissible G).IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  choose d e using hf
  let a (i : I) : arrow G (d i) ≅ Arrow.mk (f i) := Classical.choice (e i)
  let eA := Limits.Sigma.mapIso (fun i => Arrow.leftFunc.mapIso (a i))
  let eB := Limits.Sigma.mapIso (fun i => Arrow.rightFunc.mapIso (a i))
  have h : (Limits.Sigma.map (fun i => inc G (d i).A)) ≫ eB.hom =
      eA.hom ≫ Limits.Sigma.map f := by
    change Limits.Sigma.map (fun i => inc G (d i).A) ≫
        Limits.Sigma.map (fun i => (a i).hom.right) =
      Limits.Sigma.map (fun i => (a i).hom.left) ≫ Limits.Sigma.map f
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    congr 1
    funext i
    exact (a i).hom.w.symm
  have e' : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      Arrow.mk (Limits.Sigma.map f) := Arrow.isoMk eA eB h.symm
  have e₀ : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      arrow G (sumData d) := Arrow.isoMk (oldCoprodIso (G := G) d)
        (posetCoprodIso (G := G) (fun i => (d i).B)) (coprod_inc d).symm
  exact ⟨sumData d, ⟨e₀.symm ≪≫ e'⟩⟩

instance : MorphismProperty.IsStableUnderCoproducts.{u} (Admissible G) where

variable (h : PosetComparison G N adj)
include h

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma poset_attachment_invariance (d : PosetAttachment.{u})
    {X Y X' Y' : C}
    (a : posetObj G d.A ⟶ X) (j : X ⟶ Y) (v : posetObj G d.B ⟶ Y)
    (sc : IsPushout a (inc G d.A) j v)
    (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y') (v' : posetObj G d.B ⟶ Y')
    (sc' : IsPushout (a ≫ f) (inc G d.A) j' v')
    (hj : j ≫ g = f ≫ j') (hv : v ≫ g = v')
    (hf : W N f) : W N g := by
  let b := N.map a
  let i := N.map (inc G d.A)
  have : Mono i := inc_mono h d.A d.lower
  let ss := IsPushout.of_hasPushout b i
  let ss' := IsPushout.of_hasPushout (b ≫ N.map f) i
  let t : pushout b i ⟶ N.obj Y := ss.desc (N.map j) (N.map v) (by
    rw [← N.map_comp, ← N.map_comp, sc.w])
  let t' : pushout (b ≫ N.map f) i ⟶ N.obj Y' := ss'.desc (N.map j') (N.map v') (by
    rw [← N.map_comp, ← N.map_comp, ← N.map_comp, sc'.w])
  have ht := GeometricRecognition.weak_local t
    (h.comparison d.A d.lower d.retraction d.adjunction a j v
      sc ss t (ss.inl_desc _ _ _) (ss.inr_desc _ _ _))
  have ht' := GeometricRecognition.weak_local t'
    (h.comparison d.A d.lower d.retraction d.adjunction (a ≫ f) j' v'
      sc' (by simpa [b,Functor.map_comp] using ss') t' (ss'.inl_desc _ _ _) (ss'.inr_desc _ _ _))
  let s : pushout b i ⟶ pushout (b ≫ N.map f) i :=
    ss.desc (N.map f ≫ pushout.inl (b ≫ N.map f) i) (pushout.inr (b ≫ N.map f) i)
      (by simpa [Category.assoc] using ss'.w)
  have hs : Local s := local_pushout_map b i (N.map f)
    (GeometricRecognition.weak_local _ ((weak_iff_nerve N f).mp hf))
    ss ss' s (ss.inl_desc _ _ _) (ss.inr_desc _ _ _)
  have he : t ≫ N.map g = s ≫ t' := by
    apply ss.hom_ext
    · dsimp [t,s,t']
      simp only [IsPushout.inl_desc_assoc,Category.assoc,IsPushout.inl_desc]
      rw [← N.map_comp, ← N.map_comp, hj]
    · dsimp [t,s,t']
      simp only [IsPushout.inr_desc_assoc,IsPushout.inr_desc]
      rw [← N.map_comp,hv]
  apply (weak_iff_nerve N g).mpr
  apply simplicialWeakEquivalences.of_precomp t _ (local_weak t ht)
  rw [he]
  exact local_weak _ (local_comp hs ht')

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma admissible_pushout_mono {A B X Y : C}
    (i : A ⟶ B) (hi : Admissible G i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) : Mono (N.map j) := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj G d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj G d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq : IsPushout (eA.hom ≫ a) (inc G d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc G d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact h.attachment_mono d.A d.lower _ _ _ sq

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma admissible_pushout_weak {A B X Y X' Y' : C}
    (i : A ⟶ B) (hi : Admissible G i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y')
    (sq : IsPushout j f g j') (hf : W N f) :
    W N g := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj G d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj G d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq₀ : IsPushout (eA.hom ≫ a) (inc G d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc G d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact poset_attachment_invariance h d _ _ _ sq₀ f g j' _
    (sq₀.flip.paste_vert sq).flip sq.w rfl hf

lemma coproduct_boundary_pushout_mono {X Y : C}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (boundaryImages (L G))).pushouts j) : Mono (N.map j) := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout_mono h i
    ((Admissible G).coproducts_le _ (MorphismProperty.coproducts_monotone boundary_admissible _ hi))
    a j v sc

lemma coproduct_boundary_pushout_weak {X Y X' Y' : C}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (boundaryImages (L G))).pushouts j)
    (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y')
    (sq : IsPushout j f g j') (hf : W N f) :
    W N g := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout_weak h i
    ((Admissible G).coproducts_le _ (MorphismProperty.coproducts_monotone boundary_admissible _ hi))
    a j v sc f g j' sq hf

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Boundaries
open CategoryTheory Limits MorphismProperty
open KanLocal SubdividedUnit

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

abbrev Cells (G : SSet.{u} ⥤ C) : MorphismProperty (C) :=
  (MorphismProperty.coproducts.{u} (boundaryImages (L G))).pushouts

omit h [HasColimitsOfSize.{u,u} C] [PreservesFilteredColimitsOfSize.{u,u} N] in
lemma weak_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    W N f := by
  change simplicialWeakEquivalences ((R N).map f)
  exact simplicialWeakEquivalences.of_isIso _

lemma sequential_pushout_weak {X Y X' : C}
    (i : X ⟶ Y) (ht : (Cells G).TransfiniteCompositionOfShape ℕ i)
    (f : X ⟶ X') (hf : W N f) :
    W N (pushout.inl i f) := by
  let K := G
  let F := ht.F
  let a : (Functor.const ℕ).obj X ⟶ F := {
    app n := ht.isoBot.inv ≫ F.map (homOfLE (Nat.zero_le n))
    naturality n m u := by
      change 𝟙 X ≫ (ht.isoBot.inv ≫ F.map _) = (ht.isoBot.inv ≫ F.map _) ≫ F.map u
      rw [Category.id_comp,Category.assoc,← F.map_comp]
      rfl }
  have ha (n m : ℕ) (u : n ⟶ m) : a.app n ≫ F.map u = a.app m := by
    simpa using (a.naturality u).symm
  let U := Under.lift F a
  let G := U ⋙ CategoryTheory.Under.pushout f ⋙ Under.forget X'
  let e : F ⟶ G := {
    app n := pushout.inl (a.app n) f
    naturality n m u := by
      simp [G,U,CategoryTheory.Under.pushout,Under.lift,pushout.inl_desc] }
  have sq (n m : ℕ) (u : n ⟶ m) :
      IsPushout (F.map u) (e.app n) (e.app m) (G.map u) := by
    have sb : IsPushout (a.app n ≫ F.map u) f (e.app m)
        (pushout.inr (a.app n) f ≫ G.map u) := by
      have hg : pushout.inr (a.app n) f ≫ G.map u = pushout.inr (a.app m) f := by
        simp [G,U,CategoryTheory.Under.pushout,Under.lift,pushout.inr_desc]
      rw [hg, ha n m u]
      exact IsPushout.of_hasPushout _ _
    exact sb.of_left (e.naturality u) (IsPushout.of_hasPushout _ _)
  have hF (n : ℕ) : Cells K (F.map (homOfLE (Nat.le_succ n))) := ht.map_mem n (by simp)
  have hG (n : ℕ) : Cells K (G.map (homOfLE (Nat.le_succ n))) :=
    MorphismProperty.of_isPushout (sq n (n+1) (homOfLE (Nat.le_succ n))).flip (hF n)
  have he (n : ℕ) : W N (e.app n) := by
    induction n with
    | zero =>
      have : IsIso (a.app 0) := by
        change IsIso (ht.isoBot.inv ≫ F.map (𝟙 0))
        infer_instance
      have : IsIso (pushout.inr (a.app 0) f) := by infer_instance
      apply (W N).of_precomp (a.app 0) _
        (weak_iso (N := N) _)
      change W N (a.app 0 ≫ pushout.inl (a.app 0) f)
      rw [pushout.condition]
      exact (W N).comp_mem _ _ hf
        (weak_iso (N := N) _)
    | succ n ih =>
      exact coproduct_boundary_pushout_weak h _ (hF n) _ _ _
        (sq n (n+1) (homOfLE (Nat.le_succ n))) ih
  have hp (n : ℕ) : a.app n ≫ ht.incl.app n = i := by
    dsimp [a]
    rw [Category.assoc]
    have hn := ht.incl.naturality (homOfLE (Nat.zero_le n))
    dsimp at hn
    rw [hn,Category.comp_id]
    exact ht.fac
  let cU := Under.liftCocone F a ⟨Y,ht.incl⟩ i hp
  have hcU : IsColimit cU := Under.isColimitLiftCocone F a _ i hp ht.isColimit
  let cG := (Under.forget X').mapCocone ((CategoryTheory.Under.pushout f).mapCocone cU)
  have hcG : IsColimit cG := isColimitOfPreserves _ (isColimitOfPreserves _ hcU)
  let FN := F ⋙ N
  let GN := G ⋙ N
  let eN : FN ⟶ GN := Functor.whiskerRight e N
  have hn : Local (colim.map eN) := local_colimit_nat FN GN eN
    (fun n => coproduct_boundary_pushout_mono h _ (hF n))
    (fun n => coproduct_boundary_pushout_mono h _ (hG n))
    (fun n => GeometricRecognition.weak_local _
      ((weak_iff_nerve N (e.app n)).mp (he n)))
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcFN : IsColimit (N.mapCocone ⟨Y,ht.incl⟩) := isColimitOfPreserves N ht.isColimit
  have hcGN : IsColimit (N.mapCocone cG) := isColimitOfPreserves N hcG
  let eF : N.obj Y ≅ colimit FN := hcFN.coconePointUniqueUpToIso (colimit.isColimit FN)
  let eG : N.obj (pushout i f) ≅ colimit GN :=
    hcGN.coconePointUniqueUpToIso (colimit.isColimit GN)
  have eFι (n : ℕ) : N.map (ht.incl.app n) ≫ eF.hom = colimit.ι FN n :=
    hcFN.comp_coconePointUniqueUpToIso_hom (colimit.isColimit FN) n
  have eGι (n : ℕ) : colimit.ι GN n ≫ eG.inv = N.map (cG.ι.app n) :=
    hcGN.comp_coconePointUniqueUpToIso_inv (colimit.isColimit GN) n
  have eqn : N.map (pushout.inl i f) = eF.hom ≫ colim.map eN ≫ eG.inv := by
    apply hcFN.hom_ext
    intro n
    change N.map (ht.incl.app n) ≫ _ = N.map (ht.incl.app n) ≫ _
    rw [← Category.assoc, ← Category.assoc,
      eFι n, colimit.ι_map, Category.assoc, eGι n]
    change N.map (ht.incl.app n) ≫ N.map (pushout.inl i f) =
      N.map (e.app n) ≫ N.map (cG.ι.app n)
    rw [← N.map_comp, ← N.map_comp]
    congr 1
    simp [e,cG,cU,CategoryTheory.Under.pushout,Under.lift,Under.liftCocone]
    exact (pushout.inl_desc _ _ _).symm
  apply (weak_iff_nerve N _).mpr
  rw [eqn]
  exact local_weak _ (local_comp (local_iso _) (local_comp hn (local_iso _)))

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable [IsCardinalForSmallObjectArgument (boundaryImages (L G)) Cardinal.aleph0.{u}]

lemma cofibration_pushout_weak {X Y X' : C}
    (i : X ⟶ Y) (hi : Cof N i)
    (f : X ⟶ X') (hf : W N f) :
    W N (pushout.inl i f) := by
  let I := boundaryImages (L G)
  let κ := Cardinal.aleph0.{u}
  let k := SmallObject.ιObj I κ i
  let p := SmallObject.πObj I κ i
  have hp : Fib N p ∧ W N p := by
    have h := SmallObject.rlp_πObj I κ i
    change (boundaryImages (L G)).rlp p at h
    rw [boundaryImages_right_class (transferredAdjunction adj)] at h
    exact h
  have : HasLiftingProperty i p := hi p hp
  have fac : k ≫ p = i := SmallObject.ιObj_πObj I κ i
  let sq : CommSq k i p (𝟙 Y) := ⟨by simpa using fac⟩
  let s := sq.lift
  have hs : i ≫ s = k := sq.fac_left
  have hs' : s ≫ p = 𝟙 Y := sq.fac_right
  have hk : Nonempty ((Cells G).TransfiniteCompositionOfShape ℕ k) := by
    let e : ℕ ≃o Cardinal.aleph0.{u}.ord.ToType := ULift.orderIso.{u}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
    have h := SmallObject.transfiniteCompositionsOfShape_ιObj I κ i
    rw [← MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso _ e] at h
    exact h
  have hw : W N (pushout.inl k f) :=
    sequential_pushout_weak h k hk.some f hf
  let s' : pushout i f ⟶ pushout k f :=
    pushout.desc (s ≫ pushout.inl k f) (pushout.inr k f) (by
      rw [← Category.assoc,hs,pushout.condition])
  let p' : pushout k f ⟶ pushout i f :=
    pushout.desc (p ≫ pushout.inl i f) (pushout.inr i f) (by
      rw [← Category.assoc,fac,pushout.condition])
  have hsp : s' ≫ p' = 𝟙 (pushout i f) := by
    apply pushout.hom_ext
    · dsimp [s',p']
      simp only [pushout.inl_desc_assoc,Category.assoc,pushout.inl_desc,Category.comp_id]
      rw [← Category.assoc,hs',Category.id_comp]
    · dsimp [s',p']
      simp only [pushout.inr_desc_assoc,pushout.inr_desc,Category.comp_id]
  let r : RetractArrow (pushout.inl i f) (pushout.inl k f) := {
    i := Arrow.homMk s s' (by simp [s',pushout.inl_desc])
    r := Arrow.homMk p p' (by simp [p',pushout.inl_desc])
    retract := by
      apply Arrow.hom_ext
      · exact hs'
      · exact hsp }
  exact (W N).of_retract r hw

theorem left_proper : LeftProperFor (W N)
    (Cof N) := by
  intro A B X Y i f g j sq hi hf
  rw [← sq.inl_isoPushout_inv]
  exact (W N).comp_mem _ _
    (cofibration_pushout_weak h i hi f hf)
    (weak_iso (N := N) _)

end Thomason.AbstractTransfer.Boundaries

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {C : Type v} [Category.{u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

lemma unit_weak (K : SSet.{u}) :
    simplicialWeakEquivalences ((transferredAdjunction adj).unit.app K) := by
  change simplicialWeakEquivalences
    ((SSet.sdExAdjunction.comp SSet.sdExAdjunction).unit.app K ≫
      (SSet.ex ⋙ SSet.ex).map (adj.unit.app ((SSet.sd ⋙ SSet.sd).obj K)))
  exact simplicialWeakEquivalences.comp_mem _ _ (QuillenCriterion.sdExSquared_unit_weak K)
    ((Subdivision.exSquared_map_weak_iff _).mpr
      (KanLocal.local_weak _ (subdivided_unit_local h K)))

theorem adjoint_weak_iff (K : SSet.{u}) (Y : C) (f : (L G).obj K ⟶ Y) :
    W N f ↔ simplicialWeakEquivalences ((transferredAdjunction adj).homEquiv K Y f) := by
  change simplicialWeakEquivalences ((R N).map f) ↔
    simplicialWeakEquivalences ((transferredAdjunction adj).unit.app K ≫ (R N).map f)
  constructor
  · exact simplicialWeakEquivalences.comp_mem _ _ (unit_weak h K)
  · exact simplicialWeakEquivalences.of_precomp _ _ (unit_weak h K)

lemma left_preserves_weak {K K' : SSet.{u}} (f : K ⟶ K')
    (hf : simplicialWeakEquivalences f) : W N ((L G).map f) := by
  apply simplicialWeakEquivalences.of_precomp
    ((transferredAdjunction adj).unit.app K) _ (unit_weak h K)
  change simplicialWeakEquivalences
    ((transferredAdjunction adj).unit.app K ≫ (L G ⋙ R N).map f)
  rw [← (transferredAdjunction adj).unit.naturality f]
  exact simplicialWeakEquivalences.comp_mem _ _ hf (unit_weak h K')

variable [HasLimitsOfSize.{u,u} C] [HasColimitsOfSize.{u,u} C]
variable [IsLocallyPresentable.{u} C]
variable [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}]
variable [IsCardinalForSmallObjectArgument (boundaryImages (L G)) Cardinal.aleph0.{u}]

def exactEndpoint : ExactModelEndpoint (L G) (R N) (transferredAdjunction adj) where
  model := model h
  weak_eq := rfl
  fib_eq := rfl
  cof_eq := rfl
  generating_cofibrations := boundaryImages_right_class (transferredAdjunction adj)
  generating_trivial_cofibrations := hornImages_rlp (transferredAdjunction adj)
  weak_factorization_one := first_wfs h
  weak_factorization_two := transferred_second_wfs (transferredAdjunction adj)
  complete := inferInstance
  cocomplete := inferInstance
  locallyPresentable := inferInstance
  leftProper := Boundaries.left_proper h
  rightProper := transferred_right_proper (transferredAdjunction adj)
  leftQuillen f hm := by
    let := hm
    exact ⟨left_preserves_cofibrations (transferredAdjunction adj) f,
      left_preserves_weak h f⟩
  quillenEquivalence K Y _ f := adjoint_weak_iff h K Y f

end Thomason.AbstractTransfer

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits AbstractTransfer
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem omegaPosetComparison (T : RightIntervalExtension.{u}) :
    PosetComparison categorification.{u} streetNerveFunctor categorificationAdjunction := by
  exact {
    unit_weak := posetCategorificationUnit_weakEquivalence
    attachment_mono := OmegaAttachmentComparison.nerve_attachment_mono
    comparison := OmegaAttachmentComparison.gray_comparison_local T }

theorem finitePosetComparison (T : RightIntervalExtension.{u}) (n : ℕ) (hn : 1 ≤ n) :
    PosetComparison (categorificationFinite.{u} n) (streetNerveFinite n)
      (categorificationFiniteAdjunction n) := by
  let := T.rightAdjoint
  exact {
    unit_weak := posetCategorificationFiniteUnit_weakEquivalence n hn
    attachment_mono := AttachmentComparison.finite_nerve_attachment_mono n hn
    comparison := AttachmentComparison.gray_comparison_local T
      T.tensor.rightAdjoint (Adjunction.ofIsLeftAdjoint T.tensor) n hn }

def omegaEndpointOfGray (T : RightIntervalExtension.{u}) :
    ExactModelEndpoint thomasonLeft.{u} thomasonRight thomasonAdjunction := by
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (hornImages (L categorification.{u})) Cardinal.aleph0.{u} := thomasonHorn_smallCardinal
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (boundaryImages (L categorification.{u})) Cardinal.aleph0.{u} := thomasonBoundary_smallCardinal
  exact AbstractTransfer.exactEndpoint (omegaPosetComparison T)

def finiteEndpointOfGray (T : RightIntervalExtension.{u}) (n : ℕ) (hn : 1 ≤ n) :
    ExactModelEndpoint (thomasonLeftFinite.{u} n) (thomasonRightFinite n)
      (thomasonFiniteAdjunction n) := by
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (hornImages (L (categorificationFinite.{u} n))) Cardinal.aleph0.{u} := thomasonHornFinite_smallCardinal n
  letI : MorphismProperty.IsCardinalForSmallObjectArgument
      (boundaryImages (L (categorificationFinite.{u} n))) Cardinal.aleph0.{u} := thomasonBoundaryFinite_smallCardinal n
  exact AbstractTransfer.exactEndpoint (finitePosetComparison T n hn)

theorem fullMain_of_rightIntervalExtension : RightIntervalExtensionExists.{u} → FullMain.{u} := by
  rintro ⟨T⟩
  exact ⟨⟨KanQuillen.geometricModel⟩, ⟨omegaEndpointOfGray T⟩,
    fun n hn => ⟨finiteEndpointOfGray T n hn⟩⟩
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

inductive RectangleCell (n : ℕ) : Type u
  | endpoint : Bool → Table (complex.{u} (n+1)) → RectangleCell n
  | edge : Bool → RectangleCell n
  | diagonal : Table (K.{u} n) → RectangleCell n

def RectangleCell.eval {n : ℕ} : RectangleCell.{u} n → Table (K.{u} (n+1))
  | .endpoint a x => atEnd a x
  | .edge a => verticalTable (vertex n a)
  | .diagonal x => up x

def intervalLabel {n : ℕ} (t : Table (K.{u} n)) (b : Bool) : ℤ :=
  mass n 0 (sideRow t true 0 b)

@[simp] lemma intervalLabel_end {n : ℕ} (a b : Bool) (x : Table (complex.{u} n)) :
    intervalLabel (atEnd a x) b = if a then 1 else 0 := by
  cases a <;> simp [intervalLabel, sideRow, atEnd, Hom.table, cylinderEndpoint,
    cylinderEndpointMap, table_mass_zero]
  exact map_zero (mass.{u} n 0)

@[simp] lemma intervalLabel_vertical {n : ℕ} (x : Table (complex.{u} n)) (b : Bool) :
    intervalLabel (verticalTable x) b = if b then 1 else 0 := by
  cases b <;> simp [intervalLabel, sideRow, verticalTable, verticalRow, table_mass_zero]
  exact map_zero (mass.{u} n 0)

@[simp] lemma intervalLabel_up {n : ℕ} (x : Table (K.{u} n)) (b : Bool) :
    intervalLabel (up x) b = if b then 1 else 0 := by
  cases b <;> simp [intervalLabel, sideRow, diagonalRow]
  exact map_zero (mass (n+1) 0)

@[simp] lemma project_end {n : ℕ} (a : Bool) (x : Table (complex.{u} n)) :
    project (atEnd a x) = x := by
  ext p b
  cases p <;> cases a <;>
    simp [project, atEnd, Hom.table, cylinderProjection, cylinderProjectionMap,
      cylinderEndpoint, cylinderEndpointMap]

@[simp] lemma project_vertical_vertex (n : ℕ) (a : Bool) :
    project (verticalTable (vertex.{u} n a)) = vertex n a := by
  ext p b
  cases p with
  | zero => cases b <;> simp [project, Hom.table, cylinderProjection,
      cylinderProjectionMap, verticalTable, verticalRow]
  | succ p =>
    simp only [project_row, sideRow, Bool.false_eq_true, ite_false, ite_true,
      verticalTable, verticalRow, vertex_succ]
    split_ifs <;> cases b <;> simp

@[simp] lemma vertex_label (n : ℕ) (a b : Bool) :
    ((vertex.{u} n a).row 0 b).val ⟨true⟩ = if a then 1 else 0 := by
  cases a <;> simp

@[simp] lemma project_up_label {n : ℕ} (x : Table (K.{u} n)) (b : Bool) :
    ((project (up x)).row 0 b).val ⟨true⟩ = if b then 1 else 0 := by
  cases b <;> simp [project, Hom.table, cylinderProjection, cylinderProjectionMap,
    diagonalRow]

lemma vertex_injective (n : ℕ) : Function.Injective (vertex.{u} n) := by
  intro a b h
  have h' := congrArg (fun t : Table (complex (n+1)) => (t.row 0 false).val ⟨true⟩) h
  simp only [vertex_label] at h'
  cases a <;> cases b <;> simp_all

lemma RectangleCell.eval_injective (n : ℕ) : Function.Injective (RectangleCell.eval.{u} (n := n)) := by
  intro x y h
  have hs := congrArg (fun t => intervalLabel t false) h
  have ht := congrArg (fun t => intervalLabel t true) h
  cases x with
  | endpoint a x =>
    cases y with
    | endpoint b y =>
      have hab : a = b := by cases a <;> cases b <;> simp only [RectangleCell.eval, intervalLabel_end,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
      subst b
      congr 1
      simpa [RectangleCell.eval] using congrArg project h
    | edge b => cases a <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_vertical,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | diagonal y => cases a <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_up,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
  | edge a =>
    cases y with
    | endpoint b y => cases b <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_vertical,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | edge b =>
      have hv : vertex n a = vertex n b := by simpa [RectangleCell.eval] using congrArg project h
      exact congrArg RectangleCell.edge (vertex_injective n hv)
    | diagonal y =>
      have hs := congrArg (fun t => ((project t).row 0 false).val ⟨true⟩) h
      have ht := congrArg (fun t => ((project t).row 0 true).val ⟨true⟩) h
      cases a <;> simp only [RectangleCell.eval,
        project_vertical_vertex, project_up_label, vertex_label, Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
  | diagonal x =>
    cases y with
    | endpoint b y => cases b <;> simp only [RectangleCell.eval, intervalLabel_end, intervalLabel_up,
        Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | edge b =>
      have hs := congrArg (fun t => ((project t).row 0 false).val ⟨true⟩) h
      have ht := congrArg (fun t => ((project t).row 0 true).val ⟨true⟩) h
      cases b <;> simp only [RectangleCell.eval,
        project_vertical_vertex, project_up_label, vertex_label, Bool.false_eq_true, ite_true, ite_false] at hs ht <;> simp_all
    | diagonal y => exact congrArg RectangleCell.diagonal (up_injective n h)

lemma RectangleCell.eval_surjective (n : ℕ) : Function.Surjective (RectangleCell.eval.{u} (n := n)) := by
  intro t
  rcases table_cases t with ⟨a,he⟩ | ⟨a,he⟩ | hd
  · exact ⟨.endpoint a (project t), he.symm⟩
  · exact ⟨.edge a, he.symm⟩
  · exact ⟨.diagonal (down t hd), up_down t hd⟩

def rectangleEquiv (n : ℕ) : RectangleCell.{u} n ≃ Table (K.{u} (n+1)) :=
  Equiv.ofBijective RectangleCell.eval ⟨RectangleCell.eval_injective n, RectangleCell.eval_surjective n⟩

@[simp] lemma rectangleEquiv_apply (n : ℕ) (x : RectangleCell.{u} n) :
    rectangleEquiv n x = x.eval := rfl

end Thomason.GrayRecursive

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive
open DirectedComplex DirectedComplex.Table GlobeComplex

lemma globe_succ_cases (n : ℕ) (x : Table (complex.{u} (n+1))) :
    (∃ a, x = vertex n a) ∨ ∃ y : Table (complex.{u} n), x = suspendTable y := by
  obtain ⟨p,a,hp,he⟩ := table_classification x
  cases p with
  | zero => exact Or.inl ⟨a,he⟩
  | succ p => exact Or.inr ⟨truncate p a (topTable n), he.trans (suspendTable_eq_face (n := n) (k := p) a).symm⟩

@[simp] lemma atEnd_truncate {n : ℕ} (a b : Bool) (x : Table (complex.{u} n)) (k : ℕ) :
    truncate k b (atEnd a x) = atEnd a (truncate k b x) := by
  exact ((complex n).cylinderEndpoint a).table_truncate k b x |>.symm

@[simp] lemma vertex_truncate (n k : ℕ) (a b : Bool) :
    truncate k b (vertex.{u} n a) = vertex n a := by
  simp [vertex, truncate_truncate]

@[simp] lemma edge_truncate_zero (n : ℕ) (a b : Bool) :
    truncate 0 b (verticalTable (vertex.{u} n a)) = atEnd b (vertex n a) := by
  ext p e
  cases p with
  | zero => cases b <;> simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      verticalTable, verticalRow]
  | succ p => simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap]; rfl

@[simp] lemma edge_truncate_succ (n k : ℕ) (a b : Bool) :
    truncate (k+1) b (verticalTable (vertex.{u} n a)) = verticalTable (vertex n a) := by
  have h : truncate 1 false (verticalTable (vertex.{u} n a)) = verticalTable (vertex n a) :=
    vertical_fixed (vertex n a) (vertex_truncate n 0 a false)
  have he := (K (n+1)).nu.face_of_fixed h (show 1 ≤ k+1 by omega) b
  cases b <;> exact he

@[simp] lemma up_truncate_zero {n : ℕ} (b : Bool) (x : Table (K.{u} n)) :
    truncate 0 b (up x) = atEnd b (vertex n b) := by
  ext p e
  cases p with
  | zero => cases b <;> simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap,
      diagonalRow]
  | succ p => simp [atEnd, Hom.table, cylinderEndpoint, cylinderEndpointMap]; rfl

@[simp] lemma up_truncate_succ {n : ℕ} (k : ℕ) (b : Bool) (x : Table (K.{u} n)) :
    truncate (k+1) b (up x) = up (truncate k b x) := (up_truncate x k b).symm

@[simp] lemma suspend_truncate_zero {n : ℕ} (b : Bool) (x : Table (complex.{u} n)) :
    truncate 0 b (suspendTable x) = vertex n b := by
  ext p e
  cases p <;> simp

@[simp] lemma atEnd_vertex_eq (n : ℕ) (a b c d : Bool) :
    atEnd a (vertex.{u} n b) = atEnd c (vertex n d) ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hr : RectangleCell.endpoint a (vertex n b) = RectangleCell.endpoint c (vertex n d) :=
      RectangleCell.eval_injective n h
    obtain ⟨rfl,hbd⟩ := RectangleCell.endpoint.inj hr
    exact ⟨rfl, vertex_injective n hbd⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma nonobject_cases {n : ℕ} (x : Table (K.{u} (n+1)))
    (hx : truncate 0 false x ≠ x) :
    (∃ a, ∃ y : Table (complex.{u} n), x = atEnd a (suspendTable y)) ∨
      (∃ a, x = verticalTable (vertex n a)) ∨ ∃ y : Table (K.{u} n), x = up y := by
  obtain ⟨r,rfl⟩ := RectangleCell.eval_surjective n x
  cases r with
  | endpoint a x =>
    rcases globe_succ_cases n x with ⟨b,rfl⟩ | ⟨y,rfl⟩
    · exact False.elim (hx (by simp [RectangleCell.eval]))
    · exact Or.inl ⟨a,y,rfl⟩
  | edge a => exact Or.inr (Or.inl ⟨a,rfl⟩)
  | diagonal x => exact Or.inr (Or.inr ⟨x,rfl⟩)

def RectangleCell.truncate {n : ℕ} (k : ℕ) (b : Bool) : RectangleCell.{u} n → RectangleCell.{u} n
  | .endpoint a x => .endpoint a (DirectedComplex.Table.truncate (k+1) b x)
  | .edge a => .edge a
  | .diagonal x => .diagonal (DirectedComplex.Table.truncate k b x)

@[simp] lemma RectangleCell.eval_truncate {n : ℕ} (k : ℕ) (b : Bool) (x : RectangleCell.{u} n) :
    (x.truncate k b).eval = DirectedComplex.Table.truncate (k+1) b x.eval := by
  cases x <;> simp [RectangleCell.eval, RectangleCell.truncate]

lemma positive_matching_iff {n : ℕ} (k : ℕ) (x y : RectangleCell.{u} n) :
    DirectedComplex.Table.truncate (k+1) true x.eval =
        DirectedComplex.Table.truncate (k+1) false y.eval ↔
      x.truncate k true = y.truncate k false := by
  rw [← RectangleCell.eval_truncate, ← RectangleCell.eval_truncate]
  exact (RectangleCell.eval_injective n).eq_iff

end Thomason.GrayRecursive

end

end OAI

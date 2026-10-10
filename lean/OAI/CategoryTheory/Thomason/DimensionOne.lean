import Mathlib
import OAI.CategoryTheory.Thomason.KanQuillen

namespace OAI

/-! Dimension One. -/

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason

lemma transferred_right_proper {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    RightProperFor (simplicialWeakEquivalences.inverseImage R)
      (simplicialFibrations.inverseImage R) := by
  let := adj.rightAdjoint_preservesLimits
  intro A B X Y f g p q sq hq hp
  exact GeometricRecognition.right_proper _ _ _ _ (sq.map R) hq hp

lemma left_preserves_cofibrations {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R)
    {K K' : SSet.{u}} (f : K ⟶ K') [Mono f] :
    (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R).llp
      (L.map f) := by
  intro A B p hp
  apply (adj.hasLiftingProperty_iff f p).mpr
  have h : SSet.modelCategoryQuillen.I.rlp (R.map p) := by
    rw [GeometricRecognition.boundary_right_class]
    exact hp
  rw [← SSet.rlp_monomorphisms] at h
  exact h f (show Mono f from inferInstance)

lemma leftOne_preserves_weak {K K' : SSet.{u}} (f : K ⟶ K')
    (hf : simplicialWeakEquivalences f) :
    thomasonWeakEquivalencesFinite 1 ((thomasonLeftFinite 1).map f) := by
  apply (simplicialWeakEquivalences.of_precomp
    ((thomasonFiniteAdjunction 1).unit.app K) _ (QuillenCriterion.unit_one_weak K))
  change simplicialWeakEquivalences
    ((thomasonFiniteAdjunction 1).unit.app K ≫
      (thomasonLeftFinite 1 ⋙ thomasonRightFinite 1).map f)
  rw [← (thomasonFiniteAdjunction 1).unit.naturality f]
  exact simplicialWeakEquivalences.comp_mem _ _ hf (QuillenCriterion.unit_one_weak K')
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

structure PosetAttachment where
  B : Type u
  order : PartialOrder B
  A : Set B
  lower : IsLowerSet A
  retraction : upward A →o A
  retract : ∀ a : A, retraction ⟨a.val,a.val,a.property,le_rfl⟩ = a
  adjunction : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ retraction z
attribute [instance] PosetAttachment.order

abbrev PosetAttachment.arrow (d : PosetAttachment.{u}) := Arrow.mk (inc 1 d.A)

def Admissible : MorphismProperty (OmegaCategory.NCategory.{u} 1) :=
  fun _ _ f => ∃ d : PosetAttachment.{u}, Nonempty (d.arrow ≅ Arrow.mk f)

instance : Admissible.{u}.RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    rintro _ _ e ⟨d,⟨a⟩⟩
    exact ⟨d,⟨a ≪≫ e⟩⟩)

lemma boundary_admissible : boundaryImages (thomasonLeftFinite.{u} 1) ≤ Admissible := by
  rintro X Y f ⟨m⟩
  let d : PosetAttachment := {
    B := NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+1))))
    order := inferInstance
    A := oldSet (simplexFaces (SSet.boundary m))
    lower := oldSet_lower _
    retraction := flagRetraction _
    retract := flagRetraction_retract _
    adjunction := flagRetraction_adjunction _ }
  refine ⟨d, ⟨(Arrow.isoMk ((categorificationFinite 1).mapIso (oldFlagsIso (SSet.boundary m)))
    ((categorificationFinite 1).mapIso (Subdivision.sdTwiceSimplexIso m)) ?_).symm⟩⟩
  change (categorificationFinite 1).map _ ≫ (categorificationFinite 1).map _ =
    (categorificationFinite 1).map _ ≫ (categorificationFinite 1).map _
  rw [← Functor.map_comp, ← Functor.map_comp, oldFlagsIso_naturality]
  rfl

variable {I : Type u} (d : I → PosetAttachment.{u})

def sumData : PosetAttachment.{u} where
  B := Σ i, (d i).B
  order := inferInstance
  A := DependentPosets.old (fun i => (d i).A)
  lower := DependentPosets.old_lower _ (fun i => (d i).lower)
  retraction := DependentPosets.oldRetraction _ (fun i => (d i).retraction)
  retract := DependentPosets.oldRetraction_retract _ _ (fun i => (d i).retract)
  adjunction := DependentPosets.oldRetraction_adjunction _ _ (fun i => (d i).adjunction)
def posetCoprodIso (P : I → Type u) [∀ i, PartialOrder (P i)] :
    (∐ fun i => posetObj 1 (P i)) ≅ posetObj 1 (Σ i, P i) :=
  (PreservesCoproduct.iso (categorificationFinite 1) (fun i => nerve (P i))).symm ≪≫
    (categorificationFinite 1).mapIso (DependentPosets.iso P)

def oldCoprodIso : (∐ fun i => posetObj 1 (d i).A) ≅ posetObj 1 (sumData d).A :=
  (PreservesCoproduct.iso (categorificationFinite 1) (fun i => nerve (d i).A)).symm ≪≫
    (categorificationFinite 1).mapIso (DependentPosets.oldNerveIso (fun i => (d i).A))

@[reassoc] lemma posetCoprodIso_ι (P : I → Type u) [∀ i, PartialOrder (P i)] (i : I) :
    Sigma.ι (fun i => posetObj 1 (P i)) i ≫ (posetCoprodIso P).hom =
      (categorificationFinite 1).map (nerveMap (DependentPosets.incl P i).toFunctor) := by
  simp only [posetCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.iso_hom_ι]

@[reassoc] lemma oldCoprodIso_ι (i : I) :
    Sigma.ι (fun i => posetObj 1 (d i).A) i ≫ (oldCoprodIso d).hom =
      (categorificationFinite 1).map (nerveMap
        ((DependentPosets.oldIso (fun i => (d i).A)).toOrderEmbedding.toOrderHom.comp
          (DependentPosets.incl (fun i => (d i).A) i)).toFunctor) := by
  change Sigma.ι (fun i => (categorificationFinite 1).obj (nerve (d i).A)) i ≫
    ((PreservesCoproduct.iso (categorificationFinite 1) (fun i => nerve (d i).A)).inv ≫
      (categorificationFinite 1).map (DependentPosets.oldNerveIso (fun i => (d i).A)).hom) =
    (categorificationFinite 1).map _
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.oldNerveIso_ι]

lemma coprod_inc : Limits.Sigma.map (fun i => inc 1 (d i).A) ≫
    (posetCoprodIso (fun i => (d i).B)).hom =
    (oldCoprodIso d).hom ≫ inc 1 (sumData d).A := by
  apply Sigma.hom_ext
  intro i
  erw [Sigma.ι_map_assoc, posetCoprodIso_ι]
  erw [← Category.assoc]
  erw [oldCoprodIso_ι]
  change (categorificationFinite 1).map _ ≫ (categorificationFinite 1).map _ =
    (categorificationFinite 1).map _ ≫ (categorificationFinite 1).map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z


namespace Thomason.BoundaryProperness
open CategoryTheory Limits Simplicial
open AttachmentComparison Attachments HornAttachments SubdividedUnit KanLocal
attribute [-instance] CategoryTheory.Sigma.sigma

instance admissible_coproducts (I : Type u) : Admissible.{u}.IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  choose d e using hf
  let a (i : I) : (d i).arrow ≅ Arrow.mk (f i) := Classical.choice (e i)
  let eA := Limits.Sigma.mapIso (fun i => Arrow.leftFunc.mapIso (a i))
  let eB := Limits.Sigma.mapIso (fun i => Arrow.rightFunc.mapIso (a i))
  have h : (Limits.Sigma.map (fun i => inc 1 (d i).A)) ≫ eB.hom =
      eA.hom ≫ Limits.Sigma.map f := by
    change Limits.Sigma.map (fun i => inc 1 (d i).A) ≫
        Limits.Sigma.map (fun i => (a i).hom.right) =
      Limits.Sigma.map (fun i => (a i).hom.left) ≫ Limits.Sigma.map f
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    congr 1
    funext i
    exact (a i).hom.w.symm
  have e' : Arrow.mk (Limits.Sigma.map (fun i => inc 1 (d i).A)) ≅
      Arrow.mk (Limits.Sigma.map f) := Arrow.isoMk eA eB h.symm
  have e₀ : Arrow.mk (Limits.Sigma.map (fun i => inc 1 (d i).A)) ≅
      (sumData d).arrow := Arrow.isoMk (oldCoprodIso d)
        (posetCoprodIso (fun i => (d i).B)) (coprod_inc d).symm
  exact ⟨sumData d, ⟨e₀.symm ≪≫ e'⟩⟩

instance : MorphismProperty.IsStableUnderCoproducts.{u} Admissible.{u} where

lemma poset_attachment_invariance (d : PosetAttachment.{u})
    {X Y X' Y' : OmegaCategory.NCategory.{u} 1}
    (a : posetObj 1 d.A ⟶ X) (j : X ⟶ Y) (v : posetObj 1 d.B ⟶ Y)
    (sc : IsPushout a (inc 1 d.A) j v)
    (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y') (v' : posetObj 1 d.B ⟶ Y')
    (sc' : IsPushout (a ≫ f) (inc 1 d.A) j' v')
    (hj : j ≫ g = f ≫ j') (hv : v ≫ g = v')
    (hf : thomasonWeakEquivalencesFinite 1 f) : thomasonWeakEquivalencesFinite 1 g := by
  let b := N.map a
  let i := N.map (inc 1 d.A)
  have : Mono i := by
    let inclusion : d.A →o d.B := (OrderEmbedding.subtype d.A).toOrderHom
    let inclusionMap : nerve d.A ⟶ nerve d.B := nerveMap inclusion.toFunctor
    let ηA := η (nerve d.A)
    let ηB := η (nerve d.B)
    have : IsIso ηA := OneCat.oneUnitCatIso (Cat.of d.A)
    have : IsIso ηB := OneCat.oneUnitCatIso (Cat.of d.B)
    have : Mono inclusionMap := nerve_mono_orderMap inclusion Subtype.val_injective
    have hn : inclusionMap ≫ ηB = ηA ≫ i :=
      (categorificationFiniteAdjunction 1).unit.naturality inclusionMap
    have he : i = inv ηA ≫ inclusionMap ≫ ηB := by
      apply (cancel_epi ηA).mp
      rw [IsIso.hom_inv_id_assoc]
      exact hn.symm
    rw [he]
    infer_instance
  let ss := IsPushout.of_hasPushout b i
  let ss' := IsPushout.of_hasPushout (b ≫ N.map f) i
  let t : pushout b i ⟶ N.obj Y := ss.desc (N.map j) (N.map v) (by
    rw [← N.map_comp, ← N.map_comp, sc.w])
  let t' : pushout (b ≫ N.map f) i ⟶ N.obj Y' := ss'.desc (N.map j') (N.map v') (by
    rw [← N.map_comp, ← N.map_comp, ← N.map_comp, sc'.w])
  have ht := comparison_local_one d.A d.lower d.retraction d.retract d.adjunction a j v
    sc ss t (ss.inl_desc _ _ _) (ss.inr_desc _ _ _)
  have ht' := comparison_local_one d.A d.lower d.retraction d.retract d.adjunction (a ≫ f) j' v'
    sc' (by simpa [b,Functor.map_comp] using ss') t' (ss'.inl_desc _ _ _) (ss'.inr_desc _ _ _)
  let s : pushout b i ⟶ pushout (b ≫ N.map f) i :=
    ss.desc (N.map f ≫ pushout.inl (b ≫ N.map f) i) (pushout.inr (b ≫ N.map f) i)
      (by simpa [Category.assoc] using ss'.w)
  have hs : Local s := local_pushout_map b i (N.map f)
    (GeometricRecognition.weak_local _ ((Subdivision.thomasonWeakFinite_iff_nerve f).mp hf))
    ss ss' s (ss.inl_desc _ _ _) (ss.inr_desc _ _ _)
  have he : t ≫ N.map g = s ≫ t' := by
    apply ss.hom_ext
    · dsimp [t,s,t']
      simp only [IsPushout.inl_desc_assoc,Category.assoc,IsPushout.inl_desc]
      rw [← N.map_comp, ← N.map_comp, hj]
    · dsimp [t,s,t']
      simp only [IsPushout.inr_desc_assoc,IsPushout.inr_desc]
      rw [← N.map_comp,hv]
  apply (Subdivision.thomasonWeakFinite_iff_nerve g).mpr
  apply simplicialWeakEquivalences.of_precomp t _ (local_weak t ht)
  rw [he]
  exact local_weak _ (local_comp hs ht')

lemma admissible_pushout_mono {A B X Y : OmegaCategory.NCategory.{u} 1}
    (i : A ⟶ B) (hi : Admissible i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) : Mono (N.map j) := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj 1 d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj 1 d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq : IsPushout (eA.hom ≫ a) (inc 1 d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc 1 d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact nerve_attachment_mono d.A d.lower _ _ _ sq

lemma admissible_pushout_weak {A B X Y X' Y' : OmegaCategory.NCategory.{u} 1}
    (i : A ⟶ B) (hi : Admissible i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y')
    (sq : IsPushout j f g j') (hf : thomasonWeakEquivalencesFinite 1 f) :
    thomasonWeakEquivalencesFinite 1 g := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj 1 d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj 1 d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq₀ : IsPushout (eA.hom ≫ a) (inc 1 d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc 1 d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact poset_attachment_invariance d _ _ _ sq₀ f g j' _
    (sq₀.flip.paste_vert sq).flip sq.w rfl hf

lemma coproduct_boundary_pushout_mono {X Y : OmegaCategory.NCategory.{u} 1}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (boundaryImages (thomasonLeftFinite 1))).pushouts j) : Mono (N.map j) := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout_mono i
    (Admissible.coproducts_le _ (MorphismProperty.coproducts_monotone boundary_admissible _ hi))
    a j v sc

lemma coproduct_boundary_pushout_weak {X Y X' Y' : OmegaCategory.NCategory.{u} 1}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (boundaryImages (thomasonLeftFinite 1))).pushouts j)
    (f : X ⟶ X') (g : Y ⟶ Y') (j' : X' ⟶ Y')
    (sq : IsPushout j f g j') (hf : thomasonWeakEquivalencesFinite 1 f) :
    thomasonWeakEquivalencesFinite 1 g := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout_weak i
    (Admissible.coproducts_le _ (MorphismProperty.coproducts_monotone boundary_admissible _ hi))
    a j v sc f g j' sq hf

end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.BoundaryProperness
open AttachmentComparison SubdividedUnit KanLocal

abbrev Cells : MorphismProperty (OmegaCategory.NCategory.{u} 1) :=
  (MorphismProperty.coproducts.{u} (boundaryImages (thomasonLeftFinite 1))).pushouts

lemma weak_iso {X Y : OmegaCategory.NCategory.{u} 1} (f : X ⟶ Y) [IsIso f] :
    thomasonWeakEquivalencesFinite 1 f := by
  change simplicialWeakEquivalences ((thomasonRightFinite 1).map f)
  exact simplicialWeakEquivalences.of_isIso _

lemma sequential_pushout_weak {X Y X' : OmegaCategory.NCategory.{u} 1}
    (i : X ⟶ Y) (h : Cells.TransfiniteCompositionOfShape ℕ i)
    (f : X ⟶ X') (hf : thomasonWeakEquivalencesFinite 1 f) :
    thomasonWeakEquivalencesFinite 1 (pushout.inl i f) := by
  let F := h.F
  let a : (Functor.const ℕ).obj X ⟶ F := {
    app n := h.isoBot.inv ≫ F.map (homOfLE (Nat.zero_le n))
    naturality n m u := by
      change 𝟙 X ≫ (h.isoBot.inv ≫ F.map _) = (h.isoBot.inv ≫ F.map _) ≫ F.map u
      rw [Category.id_comp,Category.assoc,← F.map_comp]
      rfl }
  have ha (n m : ℕ) (u : n ⟶ m) : a.app n ≫ F.map u = a.app m := by
    simpa using (a.naturality u).symm
  let U := Under.lift F a
  let G := U ⋙ Under.pushout f ⋙ Under.forget X'
  let e : F ⟶ G := {
    app n := pushout.inl (a.app n) f
    naturality n m u := by
      simp [G,U,Under.pushout,Under.lift,pushout.inl_desc] }
  have sq (n m : ℕ) (u : n ⟶ m) :
      IsPushout (F.map u) (e.app n) (e.app m) (G.map u) := by
    have sb : IsPushout (a.app n ≫ F.map u) f (e.app m)
        (pushout.inr (a.app n) f ≫ G.map u) := by
      have hg : pushout.inr (a.app n) f ≫ G.map u = pushout.inr (a.app m) f := by
        simp [G,U,Under.pushout,Under.lift,pushout.inr_desc]
      rw [hg, ha n m u]
      exact IsPushout.of_hasPushout _ _
    exact sb.of_left (e.naturality u) (IsPushout.of_hasPushout _ _)
  have hF (n : ℕ) : Cells (F.map (homOfLE (Nat.le_succ n))) := h.map_mem n (by simp)
  have hG (n : ℕ) : Cells (G.map (homOfLE (Nat.le_succ n))) :=
    MorphismProperty.of_isPushout (sq n (n+1) (homOfLE (Nat.le_succ n))).flip (hF n)
  have he (n : ℕ) : thomasonWeakEquivalencesFinite 1 (e.app n) := by
    induction n with
    | zero =>
      have : IsIso (a.app 0) := by
        change IsIso (h.isoBot.inv ≫ F.map (𝟙 0))
        infer_instance
      have : IsIso (pushout.inr (a.app 0) f) := by infer_instance
      apply (thomasonWeakEquivalencesFinite 1).of_precomp (a.app 0) _
        (weak_iso _)
      change thomasonWeakEquivalencesFinite 1 (a.app 0 ≫ pushout.inl (a.app 0) f)
      rw [pushout.condition]
      exact (thomasonWeakEquivalencesFinite 1).comp_mem _ _ hf
        (weak_iso _)
    | succ n ih =>
      exact coproduct_boundary_pushout_weak _ (hF n) _ _ _
        (sq n (n+1) (homOfLE (Nat.le_succ n))) ih
  have hp (n : ℕ) : a.app n ≫ h.incl.app n = i := by
    dsimp [a]
    rw [Category.assoc]
    have hn := h.incl.naturality (homOfLE (Nat.zero_le n))
    dsimp at hn
    rw [hn,Category.comp_id]
    exact h.fac
  let cU := Under.liftCocone F a ⟨Y,h.incl⟩ i hp
  have hcU : IsColimit cU := Under.isColimitLiftCocone F a _ i hp h.isColimit
  let cG := (Under.forget X').mapCocone ((Under.pushout f).mapCocone cU)
  have hcG : IsColimit cG := isColimitOfPreserves _ (isColimitOfPreserves _ hcU)
  let FN := F ⋙ N
  let GN := G ⋙ N
  let eN : FN ⟶ GN := Functor.whiskerRight e N
  have hn : Local (colim.map eN) := local_colimit_nat FN GN eN
    (fun n => coproduct_boundary_pushout_mono _ (hF n))
    (fun n => coproduct_boundary_pushout_mono _ (hG n))
    (fun n => GeometricRecognition.weak_local _
      ((Subdivision.thomasonWeakFinite_iff_nerve (e.app n)).mp (he n)))
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcFN : IsColimit (N.mapCocone ⟨Y,h.incl⟩) := isColimitOfPreserves N h.isColimit
  have hcGN : IsColimit (N.mapCocone cG) := isColimitOfPreserves N hcG
  let eF : N.obj Y ≅ colimit FN := hcFN.coconePointUniqueUpToIso (colimit.isColimit FN)
  let eG : N.obj (pushout i f) ≅ colimit GN :=
    hcGN.coconePointUniqueUpToIso (colimit.isColimit GN)
  have eFι (n : ℕ) : N.map (h.incl.app n) ≫ eF.hom = colimit.ι FN n :=
    hcFN.comp_coconePointUniqueUpToIso_hom (colimit.isColimit FN) n
  have eGι (n : ℕ) : colimit.ι GN n ≫ eG.inv = N.map (cG.ι.app n) :=
    hcGN.comp_coconePointUniqueUpToIso_inv (colimit.isColimit GN) n
  have eqn : N.map (pushout.inl i f) = eF.hom ≫ colim.map eN ≫ eG.inv := by
    apply hcFN.hom_ext
    intro n
    change N.map (h.incl.app n) ≫ _ = N.map (h.incl.app n) ≫ _
    rw [← Category.assoc, ← Category.assoc,
      eFι n, colimit.ι_map, Category.assoc, eGι n]
    change N.map (h.incl.app n) ≫ N.map (pushout.inl i f) =
      N.map (e.app n) ≫ N.map (cG.ι.app n)
    rw [← N.map_comp, ← N.map_comp]
    congr 1
    simp [e,cG,cU,Under.pushout,Under.lift,Under.liftCocone]
    exact (pushout.inl_desc _ _ _).symm
  apply (Subdivision.thomasonWeakFinite_iff_nerve _).mpr
  rw [eqn]
  exact local_weak _ (local_comp (local_iso _) (local_comp hn (local_iso _)))
end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z
open CategoryTheory Limits MorphismProperty

namespace Thomason.BoundaryProperness
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

lemma cofibration_pushout_weak {X Y X' : OmegaCategory.NCategory.{u} 1}
    (i : X ⟶ Y) (hi : thomasonCofibrationsFinite 1 i)
    (f : X ⟶ X') (hf : thomasonWeakEquivalencesFinite 1 f) :
    thomasonWeakEquivalencesFinite 1 (pushout.inl i f) := by
  let I := boundaryImages (thomasonLeftFinite.{u} 1)
  let κ := Cardinal.aleph0.{u}
  let k := SmallObject.ιObj I κ i
  let p := SmallObject.πObj I κ i
  have hp : thomasonFibrationsFinite 1 p ∧ thomasonWeakEquivalencesFinite 1 p := by
    have h := SmallObject.rlp_πObj I κ i
    change (boundaryImages (thomasonLeftFinite 1)).rlp p at h
    rw [boundaryImages_right_class (thomasonFiniteAdjunction 1)] at h
    exact h
  have : HasLiftingProperty i p := hi p hp
  have fac : k ≫ p = i := SmallObject.ιObj_πObj I κ i
  let sq : CommSq k i p (𝟙 Y) := ⟨by simpa using fac⟩
  let s := sq.lift
  have hs : i ≫ s = k := sq.fac_left
  have hs' : s ≫ p = 𝟙 Y := sq.fac_right
  have hk : Nonempty (Cells.TransfiniteCompositionOfShape ℕ k) := by
    let e : ℕ ≃o Cardinal.aleph0.{u}.ord.ToType := ULift.orderIso.{u}.symm.trans
      (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
    have h := SmallObject.transfiniteCompositionsOfShape_ιObj I κ i
    rw [← MorphismProperty.transfiniteCompositionsOfShape_eq_of_orderIso _ e] at h
    exact h
  have hw : thomasonWeakEquivalencesFinite 1 (pushout.inl k f) :=
    sequential_pushout_weak k hk.some f hf
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
  exact (thomasonWeakEquivalencesFinite 1).of_retract r hw

theorem one : LeftProperFor (thomasonWeakEquivalencesFinite.{u} 1)
    (thomasonCofibrationsFinite 1) := by
  intro A B X Y i f g j sq hi hf
  rw [← sq.inl_isoPushout_inv]
  exact (thomasonWeakEquivalencesFinite 1).comp_mem _ _
    (cofibration_pushout_weak i hi f hf)
    (weak_iso _)
end Thomason.BoundaryProperness

end

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason

def exactEndpointOne : ExactModelEndpoint (thomasonLeftFinite.{u} 1)
    (thomasonRightFinite 1) (thomasonFiniteAdjunction 1) where
  model := modelOne
  weak_eq := rfl
  fib_eq := rfl
  cof_eq := rfl
  generating_cofibrations := boundaryImages_right_class (thomasonFiniteAdjunction 1)
  generating_trivial_cofibrations := hornImages_rlp (thomasonFiniteAdjunction 1)
  weak_factorization_one := FirstTransferredWFS.one
  weak_factorization_two := transferred_second_wfs (thomasonFiniteAdjunction 1)
  complete := inferInstance
  cocomplete := inferInstance
  locallyPresentable := inferInstance
  leftProper := BoundaryProperness.one
  rightProper := transferred_right_proper (thomasonFiniteAdjunction 1)
  leftQuillen f hm := by
    let := hm
    exact ⟨left_preserves_cofibrations (thomasonFiniteAdjunction 1) f,
      leftOne_preserves_weak f⟩
  quillenEquivalence K Y _ f := QuillenCriterion.one K Y f

theorem endpointOne : Nonempty (ExactModelEndpoint (thomasonLeftFinite.{u} 1)
    (thomasonRightFinite 1) (thomasonFiniteAdjunction 1)) := ⟨exactEndpointOne⟩
end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits MorphismProperty

namespace Thomason

theorem nerveDetection_allDimensions :
    thomasonWeakEquivalences.{u} =
      simplicialWeakEquivalences.inverseImage streetNerveFunctor ∧
    ∀ n : ℕ, thomasonWeakEquivalencesFinite.{u} n =
      simplicialWeakEquivalences.inverseImage (streetNerveFinite n) := by
  constructor
  · funext X Y f
    exact propext (Subdivision.thomasonWeak_iff_nerve f)
  · intro n
    funext X Y f
    exact propext (Subdivision.thomasonWeakFinite_iff_nerve f)

theorem rightProper_allDimensions :
    RightProperFor thomasonWeakEquivalences.{u} thomasonFibrations ∧
    ∀ n : ℕ, RightProperFor (thomasonWeakEquivalencesFinite.{u} n)
      (thomasonFibrationsFinite n) :=
  ⟨transferred_right_proper thomasonAdjunction,
    fun n => transferred_right_proper (thomasonFiniteAdjunction n)⟩

theorem boundaryGenerators_allDimensions :
    (boundaryImages thomasonLeft.{u}).rlp =
      thomasonFibrations ⊓ thomasonWeakEquivalences ∧
    ∀ n : ℕ, (boundaryImages (thomasonLeftFinite.{u} n)).rlp =
      thomasonFibrationsFinite n ⊓ thomasonWeakEquivalencesFinite n :=
  ⟨boundaryImages_right_class thomasonAdjunction,
    fun n => boundaryImages_right_class (thomasonFiniteAdjunction n)⟩

theorem hornGenerators_allDimensions :
    (hornImages thomasonLeft.{u}).rlp = thomasonFibrations ∧
    ∀ n : ℕ, (hornImages (thomasonLeftFinite.{u} n)).rlp =
      thomasonFibrationsFinite n :=
  ⟨hornImages_rlp thomasonAdjunction,
    fun n => hornImages_rlp (thomasonFiniteAdjunction n)⟩

theorem secondWFS_allDimensions :
    IsWeakFactorizationSystem thomasonCofibrations.{u}
      (thomasonFibrations ⊓ thomasonWeakEquivalences) ∧
    ∀ n : ℕ, IsWeakFactorizationSystem (thomasonCofibrationsFinite.{u} n)
      (thomasonFibrationsFinite n ⊓ thomasonWeakEquivalencesFinite n) :=
  ⟨transferred_second_wfs thomasonAdjunction,
    fun n => transferred_second_wfs (thomasonFiniteAdjunction n)⟩

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason

structure RightIntervalExtension where
  tensor : OmegaCategory.{u} ⥤ OmegaCategory.{u}
  endpoint : Bool → ((𝟭 OmegaCategory.{u}) ⟶ tensor)
  projection : tensor ⟶ (𝟭 OmegaCategory.{u})
  endpoint_projection : ∀ b, endpoint b ≫ projection = 𝟙 (𝟭 OmegaCategory.{u})
  cocontinuous : PreservesColimitsOfSize.{u,u} tensor
  rightAdjoint : tensor.IsLeftAdjoint
  simplex : ∀ (P : Type u) [LinearOrder P] [Finite P],
    tensor.obj (NormalizedChains.complex P).nu ≅
      (NormalizedChains.complex P).cylinder.nu
  simplex_natural : ∀ (P Q : Type u) [LinearOrder P] [Finite P]
      [LinearOrder Q] [Finite Q]
      (a : DirectedComplex.Hom (NormalizedChains.complex P) (NormalizedChains.complex Q)),
    tensor.map a.nu ≫ (simplex Q).hom = (simplex P).hom ≫ a.cylinder.nu
  simplex_endpoint : ∀ (P : Type u) [LinearOrder P] [Finite P] (b : Bool),
    (endpoint b).app (NormalizedChains.complex P).nu ≫ (simplex P).hom =
      ((NormalizedChains.complex P).cylinderEndpoint b).nu
  simplex_projection : ∀ (P : Type u) [LinearOrder P] [Finite P],
    (simplex P).hom ≫ (NormalizedChains.complex P).cylinderProjection.nu =
      projection.app (NormalizedChains.complex P).nu
  globe : ∀ n : ℕ, tensor.obj (GlobeComplex.complex.{u} n).nu ≅
    (GlobeComplex.complex.{u} n).cylinder.nu
  globe_natural : ∀ (n m : ℕ)
      (a : DirectedComplex.Hom (GlobeComplex.complex.{u} n) (GlobeComplex.complex.{u} m)),
    tensor.map a.nu ≫ (globe m).hom = (globe n).hom ≫ a.cylinder.nu
  globe_endpoint : ∀ (n : ℕ) (b : Bool),
    (endpoint b).app (GlobeComplex.complex.{u} n).nu ≫ (globe n).hom =
      ((GlobeComplex.complex.{u} n).cylinderEndpoint b).nu
  globe_projection : ∀ n : ℕ,
    (globe n).hom ≫ (GlobeComplex.complex.{u} n).cylinderProjection.nu =
      projection.app (GlobeComplex.complex.{u} n).nu

def RightIntervalExtensionExists : Prop := Nonempty RightIntervalExtension.{u}

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex
open CategoryTheory DirectedComplex DirectedComplex.Table

def tableRowMap {K : DirectedComplex.{v}} (n : ℕ) (t : Table K) (p : ℕ) :
    (complex.{u} n).Chain p →+ K.Chain p where
  toFun x := x.val ⟨false⟩ • t.row p false + x.val ⟨true⟩ • t.row p true
  map_zero' := by
    change (0 : chainModule.{u} n p).val ⟨false⟩ • t.row p false +
      (0 : chainModule.{u} n p).val ⟨true⟩ • t.row p true = 0
    simp
  map_add' x y := by
    change (x.val ⟨false⟩ + y.val ⟨false⟩) • t.row p false +
      (x.val ⟨true⟩ + y.val ⟨true⟩) • t.row p true =
      (x.val ⟨false⟩ • t.row p false + x.val ⟨true⟩ • t.row p true) +
        (y.val ⟨false⟩ • t.row p false + y.val ⟨true⟩ • t.row p true)
    simp only [add_smul]
    abel

lemma tableRowMap_d {K : DirectedComplex.{v}} (n : ℕ) (t : Table K)
    (p : ℕ) (x : (complex.{u} n).Chain (p+1)) :
    tableRowMap n t p ((complex n).d p x) =
      K.d p (tableRowMap n t (p+1) x) := by
  change ((complex n).d p x).val ⟨false⟩ • t.row p false +
      ((complex n).d p x).val ⟨true⟩ • t.row p true =
    K.d p (x.val ⟨false⟩ • t.row (p+1) false + x.val ⟨true⟩ • t.row (p+1) true)
  rw [complex_d_coordinate, complex_d_coordinate]
  simp only [Bool.false_eq_true, ite_false, ite_true, map_add, map_zsmul, t.boundary]
  change (-(x.val ⟨false⟩ + x.val ⟨true⟩)) • t.row p false +
      (x.val ⟨false⟩ + x.val ⟨true⟩) • t.row p true = _
  simp only [add_smul, neg_smul, smul_sub]
  abel

lemma tableRowMap_positive {K : DirectedComplex.{v}} (n : ℕ) (t : Table K)
    (p : ℕ) (x : (complex.{u} n).Chain p) (hx : x ∈ (complex n).positive p) :
    tableRowMap n t p x ∈ K.positive p := by
  change x.val ⟨false⟩ • t.row p false + x.val ⟨true⟩ • t.row p true ∈ K.positive p
  apply (K.positive p).add_mem
  · rw [← Int.toNat_of_nonneg (hx false), Nat.cast_smul_eq_nsmul]
    exact (K.positive p).nsmul_mem (t.positive p false) _
  · rw [← Int.toNat_of_nonneg (hx true), Nat.cast_smul_eq_nsmul]
    exact (K.positive p).nsmul_mem (t.positive p true) _

def tableMap {K : DirectedComplex.{v}} (n : ℕ) (t : Table K) :
    Hom (complex.{u} n) K where
  map := tableRowMap n t
  map_d := tableRowMap_d n t
  map_augmentation x := by
    change K.augmentation (x.val ⟨false⟩ • t.row 0 false +
      x.val ⟨true⟩ • t.row 0 true) = x.val ⟨false⟩ + x.val ⟨true⟩
    simp only [map_add, map_zsmul, t.augmentation, zsmul_eq_mul, Int.cast_id, mul_one]
  map_positive := tableRowMap_positive n t

lemma tableMap_nu_top {K : DirectedComplex.{v}} (n : ℕ) (t : Table K) :
    (tableMap.{u,v} n t).nu.map (topTable n) = truncate n false t := by
  change (tableMap n t).table (topTable n) = truncate n false t
  ext p b
  change tableRowMap n t p (topRow n p b) = _
  rw [truncate_row]
  by_cases hp : p < n
  · rw [ite_eq_left hp, topRow_lt n p b hp]
    cases b <;> simp [tableRowMap]
  · rw [ite_eq_right hp]
    by_cases hn : p = n
    · subst p
      rw [ite_eq_left rfl, topRow_eq]
      simp [tableRowMap]
    · rw [ite_eq_right hn, topRow_gt n p b (by omega), map_zero]

lemma tableMap_nu {K : DirectedComplex.{v}} {n : ℕ} (t : Table K)
    (ht : truncate n false t = t) :
    (tableMap.{u,v} n t).nu = lift t ht := by
  apply functor_ext
  erw [tableMap_nu_top, lift_top, ht]

def faceMap (n k : ℕ) (b : Bool) : Hom (complex.{u} k) (complex.{u} n) :=
  tableMap k (truncate k b (topTable n))

lemma faceMap_nu (n k : ℕ) (b : Bool) :
    (faceMap.{u} n k b).nu =
      lift (truncate k b (topTable n)) (by
        change truncate k false (truncate k b (topTable n)) = truncate k b (topTable n)
        simp only [truncate_truncate, lt_self_iff_false, ite_false]) :=
  tableMap_nu _ _

lemma chain_eq_topRows {n p : ℕ} (x : (complex.{u} n).Chain p) :
    x = x.val ⟨false⟩ • topRow n p false + x.val ⟨true⟩ • topRow n p true := by
  by_cases hp : p < n
  · rw [topRow_lt n p false hp, topRow_lt n p true hp]
    apply Subtype.ext
    funext ⟨i⟩
    change x.val ⟨i⟩ = x.val ⟨false⟩ * (if i = false then 1 else 0) +
      x.val ⟨true⟩ * (if i = true then 1 else 0)
    cases i <;> simp
  · by_cases hn : p = n
    · subst p
      rw [topRow_eq, topRow_eq]
      have ht := top_target_zero n x
      apply Subtype.ext
      funext ⟨i⟩
      change x.val ⟨i⟩ = x.val ⟨false⟩ * (if i = false then 1 else 0) +
        x.val ⟨true⟩ * (if i = false then 1 else 0)
      cases i <;> simp [ht]
    · rw [chain_zero (show n < p by omega) x]
      simp
      rfl

lemma hom_ext {K : DirectedComplex.{v}} {n : ℕ}
    {f g : Hom (complex.{u} n) K}
    (h : f.nu.map (topTable n) = g.nu.map (topTable n)) : f = g := by
  ext p x
  change f.table (topTable n) = g.table (topTable n) at h
  have h₀ := congrArg (fun t : Table K => t.row p false) h
  have h₁ := congrArg (fun t : Table K => t.row p true) h
  change f.map p (topRow n p false) = g.map p (topRow n p false) at h₀
  change f.map p (topRow n p true) = g.map p (topRow n p true) at h₁
  rw [chain_eq_topRows x]
  simp only [map_add, map_zsmul, h₀, h₁]

def homCellEquiv (n : ℕ) (K : DirectedComplex.{v}) :
    Hom (complex.{u} n) K ≃ K.nu.Cells n where
  toFun f := ⟨f.nu.map (topTable n), by
    change truncate n false (f.table (topTable n)) = f.table (topTable n)
    rw [← f.table_truncate, topTable_bounded]⟩
  invFun t := tableMap n t.val
  left_inv f := by
    apply hom_ext
    erw [tableMap_nu_top]
    change truncate n false (f.table (topTable n)) = f.table (topTable n)
    rw [← f.table_truncate, topTable_bounded]
  right_inv t := by
    apply Subtype.ext
    exact (tableMap_nu_top n t.val).trans t.property

lemma faceMap_top (n k : ℕ) (b : Bool) :
    (faceMap.{u} n k b).nu.map (topTable k) = truncate k b (topTable n) := by
  erw [faceMap_nu, lift_top]

@[simp] lemma faceMap_self (n : ℕ) (b : Bool) :
    faceMap.{u} n n b = Hom.id (complex n) := by
  apply hom_ext
  rw [faceMap_top]
  change truncate n b (topTable n) = topTable n
  rw [← face_nu]
  exact (complex n).nu.face_of_fixed (topTable_bounded n) (le_refl n) b

lemma faceMap_faceMap (n k j : ℕ) (hjk : j < k) (a b : Bool) :
    Hom.comp (faceMap.{u} k j a) (faceMap n k b) = faceMap n j a := by
  apply hom_ext
  change (faceMap n k b).nu.map ((faceMap k j a).nu.map (topTable j)) = _
  rw [faceMap_top]
  change (faceMap n k b).table (truncate j a (topTable k)) = _
  rw [Hom.table_truncate]
  change truncate j a ((faceMap n k b).nu.map (topTable k)) = _
  rw [faceMap_top, faceMap_top, truncate_truncate, ite_eq_left hjk]

def counitInverse (n : ℕ) : Hom (complex.{u} n) (complex n).nu.linearization :=
  tableMap n ((complex n).nu.lambdaUnit.map (topTable n))

lemma counitInverse_nu (n : ℕ) :
    (counitInverse.{u} n).nu = (complex n).nu.lambdaUnit := by
  apply functor_ext
  erw [counitInverse, tableMap_nu_top]
  change (complex n).nu.linearization.nu.source n
      ((complex n).nu.lambdaUnit.map (topTable n)) = _
  erw [← (complex n).nu.lambdaUnit.map_source]
  change (complex n).nu.lambdaUnit.map (truncate n false (topTable n)) = _
  rw [topTable_bounded]

lemma counitInverse_counit (n : ℕ) :
    Hom.comp (counitInverse.{u} n) (complex n).lambdaCounit = Hom.id (complex n) := by
  apply hom_ext
  change (complex n).lambdaCounit.nu.map ((counitInverse n).nu.map (topTable n)) = topTable n
  rw [counitInverse_nu]
  have h := lambdaNuForward_counit (Hom.id (complex.{u} n))
  change lambdaNuForward (complex n).lambdaCounit = OmegaCategory.Functor.id (complex n).nu at h
  exact congrArg (fun F => F.map (topTable n)) h

lemma counit_counitInverse (n : ℕ) :
    Hom.comp (complex.{u} n).lambdaCounit (counitInverse n) =
      Hom.id (complex n).nu.linearization := by
  apply (lambdaNuHomEquiv (complex n).nu (complex n).nu.linearization).injective
  change lambdaNuForward (Hom.comp (complex n).lambdaCounit (counitInverse n)) =
    lambdaNuForward (Hom.id (complex n).nu.linearization)
  rw [lambdaNuForward_counit, counitInverse_nu]
  rfl

def counitIso (n : ℕ) : (complex.{u} n).nu.linearization ≅ complex n where
  hom := (complex n).lambdaCounit
  inv := counitInverse n
  hom_inv_id := counit_counitInverse n
  inv_hom_id := counitInverse_counit n

end Thomason.GlobeComplex

end

end OAI

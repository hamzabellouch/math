import Mathlib
import OAI.CategoryTheory.Thomason.KanTowers

namespace OAI

/-! Posetal Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy KanPath
open SSet.modelCategoryQuillen

lemma local_colimit_nat (F G : ℕ ⥤ SSet.{u}) (f : F ⟶ G)
    (hF : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, Mono (G.map (homOfLE (Nat.le_succ n))))
    (hf : ∀ n, Local (f.app n)) : Local (colim.map f) := by
  intro K hK
  let H := internalHom.flip.obj K
  let DF := F.op ⋙ H
  let DG := G.op ⋙ H
  let d : DG ⟶ DF := Functor.whiskerRight (NatTrans.op f) H
  have hcF : IsLimit (H.mapCone (colimit.cocone F).op) :=
    isLimitOfPreserves H (colimit.isColimit F).op
  have hcG : IsLimit (H.mapCone (colimit.cocone G).op) :=
    isLimitOfPreserves H (colimit.isColimit G).op
  let eF : (ihom (colimit F)).obj K ≅ limit DF :=
    hcF.conePointUniqueUpToIso (limit.isLimit DF)
  let eG : (ihom (colimit G)).obj K ≅ limit DG :=
    hcG.conePointUniqueUpToIso (limit.isLimit DG)
  have eFπ (n : ℕ) : eF.hom ≫ limit.π DF (op n) = (pre (colimit.ι F n)).app K :=
    hcF.conePointUniqueUpToIso_hom_comp (limit.isLimit DF) (op n)
  have eGπ (n : ℕ) : eG.hom ≫ limit.π DG (op n) = (pre (colimit.ι G n)).app K :=
    hcG.conePointUniqueUpToIso_hom_comp (limit.isLimit DG) (op n)
  have hd : IsHomotopyEquivalence (lim.map d) :=
    KanTower.homotopyEquivalence_limit DG DF d
      (fun n => by change SSet.KanComplex ((ihom (G.obj n)).obj K); infer_instance)
      (fun n => by change SSet.KanComplex ((ihom (F.obj n)).obj K); infer_instance)
      (fun n => by
        change J.rlp ((pre (G.map (homOfLE (Nat.le_succ n)))).app K)
        let := hG n
        rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
        infer_instance)
      (fun n => by
        change J.rlp ((pre (F.map (homOfLE (Nat.le_succ n)))).app K)
        let := hF n
        rw [← fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
        infer_instance)
      (fun n => hf n K hK)
  have hw : (pre (colim.map f)).app K ≫ eF.hom = eG.hom ≫ lim.map d := by
    apply limit.hom_ext
    rintro ⟨n⟩
    simp only [Category.assoc, eFπ, lim_map, limMap_π]
    rw [← Category.assoc, eGπ]
    change (pre (colim.map f)).app K ≫ (pre (colimit.ι F n)).app K =
      (pre (colimit.ι G n)).app K ≫ (pre (f.app n)).app K
    rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
      colimit.ι_map]
  apply heq_of_postcomp _ eF.hom (heq_of_isIso _)
  rw [hw]
  exact heq_comp (heq_of_isIso _) hd

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits
open AttachmentComparison Attachments KanLocal

abbrev C := categorificationFinite.{u} 1
abbrev N := streetNerveFinite.{u} 1
abbrev η (X : SSet.{u}) := (categorificationFiniteAdjunction 1).unit.app X

lemma nerve_attachment_mono {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    {X Y : OmegaCategory.NCategory.{u} 1} (a : posetObj 1 A ⟶ X)
    (j : X ⟶ Y) (v : posetObj 1 B ⟶ Y) (sc : IsPushout a (inc 1 A) j v) :
    Mono (N.map j) := by
  obtain ⟨S,hS,e,he⟩ := poset_finite_sieve_attachment 1 (by decide) A hA a j v sc
  have hinc := OmegaCategory.Subcategory.inclusion_mono (Y.val.fullOn S)
  have hj : Mono ((OmegaCategory.nCategoryInclusion 1).map j) := by
    change @Mono OmegaCategory inferInstance X.val Y.val j
    rw [← he]
    infer_instance
  have : Mono j := (OmegaCategory.nCategoryInclusion 1).mono_of_mono_map hj
  let : PreservesLimits N := (categorificationFiniteAdjunction 1).rightAdjoint_preservesLimits
  infer_instance

lemma unit_local_attachment {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hr : ∀ a : A, r ⟨a.val,a.val,a.property,le_rfl⟩ = a)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {V W : SSet.{u}} (a : nerve A ⟶ V) (j : V ⟶ W) (v : nerve B ⟶ W)
    (sc : IsPushout a (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor) j v)
    (hV : Local (η V)) : Local (η W) := by
  let i : nerve A ⟶ nerve B := nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have : Mono i := nerve_mono_orderMap
    (OrderHom.Subtype.val (fun element : B => element ∈ A)) Subtype.val_injective
  have : IsIso (η (nerve A)) := OneCat.oneUnitCatIso (Cat.of A)
  have : IsIso (η (nerve B)) := OneCat.oneUnitCatIso (Cat.of B)
  let b := N.map (C.map a)
  let c := N.map (C.map i)
  let P := pushout b c
  let lV := pushout.inl b c
  let lB := pushout.inr b c
  have ss : IsPushout b c lV lB := IsPushout.of_hasPushout b c
  have ss' : IsPushout (a ≫ η V) i lV (η (nerve B) ≫ lB) := by
    apply ss.of_iso (asIso (η (nerve A))).symm (Iso.refl _)
      (asIso (η (nerve B))).symm (Iso.refl _)
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, asIso_inv]
      apply (cancel_epi (η (nerve A))).mp
      simp [b]
    · simp only [Iso.symm_hom, asIso_inv]
      apply (cancel_epi (η (nerve A))).mp
      simp only [IsIso.hom_inv_id_assoc]
      apply (cancel_mono (η (nerve B))).mp
      simp [c]
    · simp
    · simp
  let q : W ⟶ P := sc.desc (η V ≫ lV) (η (nerve B) ≫ lB) (by
    simpa [Category.assoc] using ss'.w)
  have hqV : j ≫ q = η V ≫ lV := sc.inl_desc _ _ _
  have hqB : v ≫ q = η (nerve B) ≫ lB := sc.inr_desc _ _ _
  have hq : Local q := local_pushout_map a i (η V) hV sc ss' q hqV hqB
  have cs : IsPushout (C.map a) (inc 1 A) (C.map j) (C.map v) := sc.map C
  let t : P ⟶ N.obj (C.obj W) := ss.desc (N.map (C.map j)) (N.map (C.map v)) (by
    dsimp [b,c]
    rw [← N.map_comp, ← N.map_comp]
    exact congrArg N.map cs.w)
  have htV : lV ≫ t = N.map (C.map j) := ss.inl_desc _ _ _
  have htB : lB ≫ t = N.map (C.map v) := ss.inr_desc _ _ _
  have ht : Local t := comparison_local_one A hA r hr hadj (C.map a)
    (C.map j) (C.map v) cs ss t htV htB
  have hqt : q ≫ t = η W := by
    apply sc.hom_ext
    · rw [← Category.assoc,hqV,Category.assoc,htV]
      exact ((categorificationFiniteAdjunction 1).unit.naturality j).symm
    · rw [← Category.assoc,hqB,Category.assoc,htB]
      exact ((categorificationFiniteAdjunction 1).unit.naturality v).symm
  rw [← hqt]
  exact local_comp hq ht

end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z


namespace Thomason.PosetCoproduct
open CategoryTheory Limits Opposite

@[ext] structure Piece (I P : Type u) where
  label : I
  value : P

instance {I P : Type u} [PartialOrder P] : PartialOrder (Piece I P) where
  le x y := x.label = y.label ∧ x.value ≤ y.value
  le_refl _ := ⟨rfl,le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1,h.2.trans k.2⟩
  le_antisymm _ _ h k := Piece.ext h.1 (le_antisymm h.2 k.2)

variable (I P : Type u) [PartialOrder P]
def incl (i : I) : P →o Piece I P where
  toFun p := ⟨i,p⟩
  monotone' _ _ h := ⟨rfl,h⟩
def value : Piece I P →o P where
  toFun p := p.value
  monotone' _ _ h := h.2

lemma label_const {n : SimplexCategoryᵒᵖ} (s : (nerve (Piece I P)).obj n)
    (j : Fin (n.unop.len+1)) : (s.obj j).label = (s.obj 0).label :=
  (leOfHom (s.map (homOfLE (Fin.zero_le j)))).1.symm

lemma incl_value {n : SimplexCategoryᵒᵖ} (s : (nerve (Piece I P)).obj n) :
    (nerveMap (incl I P (s.obj 0).label).toFunctor).app n
      ((nerveMap (value I P).toFunctor).app n s) = s := by
  apply nerve.ext_of_isThin
  funext j
  exact Piece.ext (label_const I P s j).symm rfl

def isColimit : IsColimit (Cofan.mk (nerve (Piece I P))
    (fun i => nerveMap (incl I P i).toFunctor)) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj n) (fun _ : I => nerve P)
    (fun i => nerveMap (incl I P i).toFunctor)).symm.toFun
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i = j := congrArg (fun s => (s.obj 0).label) h
    subst j
    have hxy : x = y := by
      apply nerve.ext_of_isThin
      funext k
      exact congrArg (fun s => (s.obj k).value) h
    subst y
    rfl
  · intro s
    exact ⟨⟨(s.obj 0).label, (nerveMap (value I P).toFunctor).app n s⟩,
      incl_value I P s⟩

def iso : (∐ fun _ : I => nerve P) ≅ nerve (Piece I P) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (isColimit I P)

@[reassoc] lemma iso_hom_ι (i : I) :
    Sigma.ι (fun _ : I => nerve P) i ≫ (iso I P).hom =
      nerveMap (incl I P i).toFunctor :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom (isColimit I P) (Discrete.mk i)

variable {P}
def old (A : Set P) : Set (Piece I P) := {x | x.value ∈ A}
lemma old_lower (A : Set P) (hA : IsLowerSet A) : IsLowerSet (old I A) :=
  fun _ _ h hx => hA h.2 hx

def oldIso (A : Set P) : Piece I A ≃o old I A where
  toFun x := ⟨⟨x.label,x.value.val⟩,x.value.property⟩
  invFun x := ⟨x.val.label,⟨x.val.value,x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def oldNerveIso (A : Set P) : (∐ fun _ : I => nerve A) ≅ nerve (old I A) :=
  iso I A ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (Piece I A))
      (β := PartOrd.of (old I A)) (oldIso I A))

@[reassoc] lemma oldNerveIso_ι (A : Set P) (i : I) :
    Sigma.ι (fun _ : I => nerve A) i ≫ (oldNerveIso I A).hom =
      nerveMap ((oldIso I A).toOrderEmbedding.toOrderHom.comp (incl I A i)).toFunctor := by
  erw [oldNerveIso, Iso.trans_hom, iso_hom_ι_assoc]
  rfl

lemma old_naturality (A : Set P) :
    Limits.Sigma.map (fun _ : I => nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor) ≫
      (iso I P).hom =
    (oldNerveIso I A).hom ≫ nerveMap (OrderEmbedding.subtype (old I A)).toOrderHom.toFunctor := by
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_map_assoc, iso_hom_ι]
  rw [← Category.assoc]
  erw [oldNerveIso_ι I A i]
  rfl

open Attachments AttachmentComparison
def oldUp (A : Set P) (z : upward (old I A)) : upward A :=
  ⟨z.val.value, by
    obtain ⟨a,ha,haz⟩ := z.property
    exact ⟨a.value,ha,haz.2⟩⟩

def oldRetraction (A : Set P) (r : upward A →o A) : upward (old I A) →o old I A where
  toFun z := ⟨⟨z.val.label, (r (oldUp I A z)).val⟩, (r (oldUp I A z)).property⟩
  monotone' _ _ h := ⟨h.1, r.monotone h.2⟩

lemma oldRetraction_retract (A : Set P) (r : upward A →o A)
    (hr : ∀ a : A, r ⟨a.val,a.val,a.property,le_rfl⟩ = a) (a : old I A) :
    oldRetraction I A r ⟨a.val,a.val,a.property,le_rfl⟩ = a := by
  apply Subtype.ext
  apply Piece.ext
  · rfl
  · exact congrArg Subtype.val (hr ⟨a.val.value,a.property⟩)

lemma oldRetraction_adjunction (A : Set P) (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    (a : old I A) (z : upward (old I A)) :
    a.val ≤ z.val ↔ a ≤ oldRetraction I A r z := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr_right (fun _ => hadj ⟨a.val.value,a.property⟩ (oldUp I A z))

end Thomason.PosetCoproduct

end

noncomputable section
universe u v w z


namespace Thomason.HornAttachments
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Subdivision

def oldSet {P : Type u} [PartialOrder P] (A : Set P) : Set (NonemptyFiniteChains P) :=
  {s | ∀ x ∈ s.finset, x ∈ A}

lemma oldSet_lower {P : Type u} [PartialOrder P] (A : Set P) : IsLowerSet (oldSet A) :=
  fun _ _ h ht => oldChains_sieve A h ht

def upwardToMeeting {P : Type u} [PartialOrder P] (A : Set P) :
    upward (oldSet A) →o MeetingChains A where
  toFun s := ⟨s.val, (meetingChains_upward A s.val).mpr (by
    obtain ⟨t,ht,hts⟩ := s.property
    exact ⟨⟨t,ht⟩,hts⟩)⟩
  monotone' _ _ h := h

def flagRetraction {P : Type u} [PartialOrder P] (A : Set P) :
    upward (oldSet A) →o oldSet A :=
  (chainIntersection A).comp (upwardToMeeting A)

lemma flagRetraction_retract {P : Type u} [PartialOrder P] (A : Set P) (a : oldSet A) :
    flagRetraction A ⟨a.val,a.val,a.property,le_rfl⟩ = a :=
  chainIntersection_retraction A a

lemma flagRetraction_adjunction {P : Type u} [PartialOrder P] (A : Set P)
    (a : oldSet A) (s : upward (oldSet A)) :
    a.val ≤ s.val ↔ a ≤ flagRetraction A s :=
  chainIntersection_adjunction A a (upwardToMeeting A s)

def simplexFaces {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    Set (NonemptyFiniteChains (ULift.{u} (Fin (m+1)))) :=
  {c | ∃ s : (orderedSimplexSubcomplex K : SSet).N,
    simplexChain (subcomplexN (orderedSimplexSubcomplex K) s).simplex = c}

def oldFlagsIso {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).obj (K : SSet.{u}) ≅ nerve (oldSet (simplexFaces K)) :=
  sdTwiceSimplexSubcomplexIso K ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (NonemptyFiniteChains (AllowedChains (orderedSimplexSubcomplex K))))
      (β := PartOrd.of (oldSet (simplexFaces K))) (chainsSubtypeOrderIso (simplexFaces K)))

lemma oldFlagsIso_naturality {m : ℕ} (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    (SSet.sd ⋙ SSet.sd).map K.ι ≫ (sdTwiceSimplexIso m).hom =
      (oldFlagsIso K).hom ≫ nerveMap (OrderEmbedding.subtype (oldSet (simplexFaces K))).toOrderHom.toFunctor := by
  rw [sdTwiceSimplexSubcomplexIso_naturality]
  rfl

end Thomason.HornAttachments

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits Simplicial PartialOrder
open Subdivision AttachmentComparison HornAttachments

abbrev D := SSet.sd.{u} ⋙ SSet.sd

def mappedCoprodIso (I : Type u) {X Y : SSet.{u}} (e : D.obj X ≅ Y) :
    D.obj (∐ fun _ : I => X) ≅ ∐ fun _ : I => Y :=
  PreservesCoproduct.iso D (fun _ : I => X) ≪≫ Sigma.mapIso (fun _ => e)

@[reassoc] lemma mappedCoprodIso_ι (I : Type u) {X Y : SSet.{u}} (e : D.obj X ≅ Y)
    (i : I) : D.map (Sigma.ι (fun _ : I => X) i) ≫ (mappedCoprodIso I e).hom =
      e.hom ≫ Sigma.ι (fun _ : I => Y) i := by
  have h : D.map (Sigma.ι (fun _ : I => X) i) ≫
      (PreservesCoproduct.iso D (fun _ : I => X)).hom =
      Sigma.ι (fun _ : I => D.obj X) i :=
    (isColimitOfHasCoproductOfPreservesColimit D (fun _ : I => X)).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit _) (Discrete.mk i)
  simp only [mappedCoprodIso, Iso.trans_hom, ← Category.assoc, h, Sigma.ι_mapIso_hom]

abbrev Faces (d : ℕ) := NonemptyFiniteChains (ULift.{u} (Fin (d+1)))
abbrev Flags (d : ℕ) := NonemptyFiniteChains (Faces.{u} d)
abbrev BoundaryFlags (d : ℕ) : Set (Flags.{u} d) :=
  oldSet (simplexFaces (SSet.boundary.{u} d))

def simplexCoprodIso (I : Type u) (d : ℕ) :
    D.obj (∐ fun _ : I => Δ[d]) ≅ nerve (PosetCoproduct.Piece I (Flags d)) :=
  mappedCoprodIso I (sdTwiceSimplexIso d) ≪≫ PosetCoproduct.iso I (Flags d)

def boundaryCoprodIso (I : Type u) (d : ℕ) :
    D.obj (∐ fun _ : I => (∂Δ[d] : SSet)) ≅
      nerve (PosetCoproduct.old I (BoundaryFlags d)) :=
  mappedCoprodIso I (oldFlagsIso (SSet.boundary d)) ≪≫
    PosetCoproduct.oldNerveIso I (BoundaryFlags d)

@[reassoc] lemma simplexCoprodIso_ι (I : Type u) (d : ℕ) (i : I) :
    D.map (Sigma.ι (fun _ : I => Δ[d]) i) ≫ (simplexCoprodIso I d).hom =
      (sdTwiceSimplexIso d).hom ≫ nerveMap (PosetCoproduct.incl I (Flags d) i).toFunctor := by
  simp only [simplexCoprodIso, Iso.trans_hom]
  erw [mappedCoprodIso_ι_assoc]
  rw [PosetCoproduct.iso_hom_ι]

@[reassoc] lemma boundaryCoprodIso_ι (I : Type u) (d : ℕ) (i : I) :
    D.map (Sigma.ι (fun _ : I => (∂Δ[d] : SSet)) i) ≫ (boundaryCoprodIso I d).hom =
      (oldFlagsIso (SSet.boundary d)).hom ≫
        nerveMap ((PosetCoproduct.oldIso I (BoundaryFlags d)).toOrderEmbedding.toOrderHom.comp
          (PosetCoproduct.incl I (BoundaryFlags d) i)).toFunctor := by
  simp only [boundaryCoprodIso, Iso.trans_hom]
  erw [mappedCoprodIso_ι_assoc, PosetCoproduct.oldNerveIso_ι]

lemma mappedCoprodIso_naturality (I : Type u) {A B A' B' : SSet.{u}}
    (f : A ⟶ B) (g : A' ⟶ B') (eA : D.obj A ≅ A') (eB : D.obj B ≅ B')
    (h : D.map f ≫ eB.hom = eA.hom ≫ g) :
    D.map (Limits.Sigma.map (fun _ : I => f)) ≫ (mappedCoprodIso I eB).hom =
      (mappedCoprodIso I eA).hom ≫ Limits.Sigma.map (fun _ : I => g) := by
  apply (isColimitOfHasCoproductOfPreservesColimit D (fun _ : I => A)).hom_ext
  rintro ⟨i⟩
  change D.map (Sigma.ι (fun _ : I => A) i) ≫ _ =
    D.map (Sigma.ι (fun _ : I => A) i) ≫ _
  rw [← Category.assoc, ← D.map_comp, Sigma.ι_map, D.map_comp, Category.assoc,
    mappedCoprodIso_ι]
  simp only [← Category.assoc]
  rw [mappedCoprodIso_ι, h]
  simp only [Category.assoc, Sigma.ι_map]

lemma boundaryCoprodIso_naturality (I : Type u) (d : ℕ) :
    D.map (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) ≫ (simplexCoprodIso I d).hom =
      (boundaryCoprodIso I d).hom ≫ nerveMap
        (OrderEmbedding.subtype (PosetCoproduct.old I (BoundaryFlags d))).toOrderHom.toFunctor := by
  have h := mappedCoprodIso_naturality I ∂Δ[d].ι
    (nerveMap (OrderEmbedding.subtype (BoundaryFlags d)).toOrderHom.toFunctor)
    (oldFlagsIso (SSet.boundary d)) (sdTwiceSimplexIso d)
    (oldFlagsIso_naturality (SSet.boundary d))
  have h' := PosetCoproduct.old_naturality I (BoundaryFlags d)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (PosetCoproduct.iso I (Flags d)).hom) h).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (fun q => (mappedCoprodIso I (oldFlagsIso (SSet.boundary d))).hom ≫ q) h').trans
    (Category.assoc _ _ _).symm)))

end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits Simplicial PartialOrder
open KanLocal AttachmentComparison HornAttachments

lemma unit_local_of_iso {X Y : SSet.{u}} (e : X ≅ Y) (hX : Local (η X)) :
    Local (η Y) := by
  have he : η Y = e.inv ≫ η X ≫ N.map (C.map e.hom) := by
    have hn : e.hom ≫ η Y = η X ≫ N.map (C.map e.hom) :=
      (categorificationFiniteAdjunction 1).unit.naturality e.hom
    rw [← hn]
    simp
  rw [he]
  exact local_comp (local_iso e.inv) (local_comp hX (local_iso _))

lemma unit_local_initial {X : SSet.{u}} (hX : IsInitial X) : Local (η X) := by
  let P := ULift.{u} Empty
  let : PartialOrder P := inferInstance
  have hP : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact (s.obj 0).down.elim)
  have : IsIso (η (nerve P)) := OneCat.oneUnitCatIso (Cat.of P)
  exact unit_local_of_iso (hP.uniqueUpToIso hX) (local_iso _)

lemma boundary_unit_successor (I : Type u) (d : ℕ) {X Y : SSet.{u}}
    (a : (∐ fun _ : I => (∂Δ[d] : SSet)) ⟶ X) (j : X ⟶ Y)
    (v : (∐ fun _ : I => Δ[d]) ⟶ Y)
    (sc : IsPushout a (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) j v)
    (hX : Local (η (D.obj X))) :
    Local (η (D.obj Y)) ∧ Mono (D.map j) ∧ Mono (N.map (C.map (D.map j))) := by
  let A := PosetCoproduct.old I (BoundaryFlags d)
  let rA := PosetCoproduct.oldRetraction I (BoundaryFlags d)
    (flagRetraction (simplexFaces (SSet.boundary d)))
  have hA : IsLowerSet A := PosetCoproduct.old_lower I _ (oldSet_lower _)
  have hrA : ∀ a : A, rA ⟨a.val,a.val,a.property,le_rfl⟩ = a :=
    PosetCoproduct.oldRetraction_retract I _ _ (flagRetraction_retract _)
  have hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ rA z :=
    PosetCoproduct.oldRetraction_adjunction I _ _ (flagRetraction_adjunction _)
  let a' := (boundaryCoprodIso I d).inv ≫ D.map a
  let v' := (simplexCoprodIso I d).inv ≫ D.map v
  let i : nerve A ⟶ nerve (PosetCoproduct.Piece I (Flags d)) :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have sq : IsPushout a' i (D.map j) v' := by
    apply (sc.map D).of_iso (boundaryCoprodIso I d) (Iso.refl _)
      (simplexCoprodIso I d) (Iso.refl _)
    · simp [a']
    · exact boundaryCoprodIso_naturality I d
    · simp
    · simp [v']
  have : Mono i := nerve_mono_orderMap
    (OrderHom.Subtype.val (fun element : PosetCoproduct.Piece I (Flags d) => element ∈ A))
    Subtype.val_injective
  refine ⟨unit_local_attachment A hA rA hrA hadj a' (D.map j) v' sq hX,
    Adhesive.mono_of_isPushout_of_mono_right sq, ?_⟩
  exact nerve_attachment_mono A hA (C.map a') (C.map (D.map j)) (C.map v') (sq.map C)

lemma unit_local_skeleton (K : SSet.{u}) (d : ℕ) :
    Local (η (D.obj ((SSet.relativeCellComplex K).F.obj d))) := by
  induction d with
  | zero =>
    apply unit_local_initial
    apply IsInitial.isInitialObj
    have h₀ : IsInitial (⊥ : K.Subcomplex).toSSet :=
      SSet.isInitialOfNotNonempty (by rintro ⟨s⟩; exact s.property)
    exact h₀.ofIso (SSet.relativeCellComplex K).isoBot.symm
  | succ d ih =>
    exact (boundary_unit_successor
      (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
      (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
      (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
      ih).1

lemma skeleton_monos (K : SSet.{u}) (d : ℕ) :
    Mono (D.map ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))) ∧
      Mono (N.map (C.map (D.map
        ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))))) :=
  (boundary_unit_successor
    (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
    (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
    (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
    (unit_local_skeleton K d)).2

theorem unit_local_one (K : SSet.{u}) : Local (η (D.obj K)) := by
  let c := SSet.relativeCellComplex K
  let F := c.F ⋙ D
  let G := c.F ⋙ D ⋙ C ⋙ N
  let f : F ⟶ G := Functor.whiskerLeft F (categorificationFiniteAdjunction 1).unit
  have hf : Local (colim.map f) := local_colimit_nat F G f
    (fun d => (skeleton_monos K d).1) (fun d => (skeleton_monos K d).2)
    (unit_local_skeleton K)
  have hcF : IsColimit (D.mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves D c.isColimit
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcG : IsColimit ((D ⋙ C ⋙ N).mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves (D ⋙ C ⋙ N) c.isColimit
  let eF : D.obj K ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj (C.obj (D.obj K)) ≅ colimit G :=
    hcG.coconePointUniqueUpToIso (colimit.isColimit G)
  have hF (d : ℕ) : D.map (c.incl.app d) ≫ eF.hom = colimit.ι F d :=
    hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) d
  have hG (d : ℕ) : colimit.ι G d ≫ eG.inv = N.map (C.map (D.map (c.incl.app d))) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit G) d
  have he : η (D.obj K) = eF.hom ≫ colim.map f ≫ eG.inv := by
    apply hcF.hom_ext
    intro d
    change D.map (c.incl.app d) ≫ η (D.obj K) =
      D.map (c.incl.app d) ≫ eF.hom ≫ colim.map f ≫ eG.inv
    rw [← Category.assoc, hF, ← Category.assoc, colimit.ι_map, Category.assoc, hG]
    exact (categorificationFiniteAdjunction 1).unit.naturality (D.map (c.incl.app d))
  rw [he]
  exact local_comp (local_iso _) (local_comp hf (local_iso _))

theorem one : OneStatement.{u} := fun K => local_weak _ (unit_local_one K)

end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition.Posetal

def Property (C : Cat.{u,u}) : Prop :=
  (∀ x y : C, Subsingleton (x ⟶ y)) ∧ (∀ x y : C, (x ⟶ y) → (y ⟶ x) → x = y)

def IsPosetal (C : Cat.{u,u}) : Prop := ∃ P : PartOrd.{u}, Nonempty (C ≅ Cat.of P)

lemma property_poset (P : PartOrd.{u}) : Property (Cat.of P) :=
  by
  change (∀ x y : P, Subsingleton (x ⟶ y)) ∧ (∀ x y : P, (x ⟶ y) → (y ⟶ x) → x = y)
  exact ⟨fun _ _ => inferInstance, fun x y f g =>
    le_antisymm (show (x : P) ≤ y from leOfHom f) (show (y : P) ≤ x from leOfHom g)⟩

lemma property_iso {C D : Cat.{u,u}} (e : C ≅ D) (hD : Property D) : Property C := by
  let F := e.hom.toFunctor
  have hi (x : C) : e.inv.toFunctor.obj (F.obj x) = x :=
    CategoryTheory.Functor.congr_obj (congrArg Cat.Hom.toFunctor e.hom_inv_id) x
  have hfaith : Function.Injective F.obj := fun _ _ h => by
    simpa! only [hi] using congrArg e.inv.toFunctor.obj h
  let : F.Faithful := (Cat.equivOfIso e).faithful_functor
  refine ⟨fun x y => ⟨fun f g => F.map_injective ((hD.1 _ _).elim _ _)⟩, ?_⟩
  intro x y f g
  exact hfaith (hD.2 _ _ (F.map f) (F.map g))

lemma isPosetal_of_property {C : Cat.{u,u}} (h : Property C) : IsPosetal C := by
  let : Quiver.IsThin C := h.1
  let e : C ≌ ThinSkeleton C := (ThinSkeleton.equivalence C).symm
  refine ⟨PartOrd.of (ThinSkeleton C), ⟨Cat.isoOfEquiv e ?_ ?_ (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)⟩⟩
  · intro x
    exact h.2 _ _ (e.unitIso.app x).inv (e.unitIso.app x).hom
  · intro y
    exact ThinSkeleton.skeletal ⟨e.counitIso.app y⟩

lemma property_of_isPosetal {C : Cat.{u,u}} (h : IsPosetal C) : Property C := by
  obtain ⟨P,⟨e⟩⟩ := h
  exact property_iso e (property_poset P)

def EdgeThin (X : SSet.{u}) : Prop :=
  ∀ s t : X _⦋1⦌, (∀ i : Fin 2, X.δ i s = X.δ i t) → s = t

def EdgeAntisym (X : SSet.{u}) : Prop :=
  ∀ s t : X _⦋1⦌, X.δ 0 s = X.δ 1 t → X.δ 1 s = X.δ 0 t → X.δ 0 s = X.δ 1 s

lemma nerve_edgeThin (C : Cat.{u,u}) (h : Property C) : EdgeThin (nerve C) := by
  let : Quiver.IsThin C := h.1
  intro s t he
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  · exact congrArg (fun a => a.obj 0) (he 1)
  · exact congrArg (fun a => a.obj 0) (he 0)

lemma nerve_edgeAntisym (C : Cat.{u,u}) (h : Property C) : EdgeAntisym (nerve C) := by
  intro s t h₀ h₁
  have e₀ : s.obj 1 = t.obj 0 := congrArg (fun a => a.obj 0) h₀
  have e₁ : s.obj 0 = t.obj 1 := congrArg (fun a => a.obj 0) h₁
  apply ComposableArrows.ext₀
  exact h.2 _ _ (eqToHom e₀ ≫ t.hom ≫ eqToHom e₁.symm) s.hom

lemma property_of_nerve_edges (C : Cat.{u,u}) (ht : EdgeThin (nerve C))
    (ha : EdgeAntisym (nerve C)) : Property C := by
  refine ⟨fun x y => ⟨fun f g => ?_⟩, ?_⟩
  · have he := ht (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g) (by
      intro i; fin_cases i <;> apply ComposableArrows.ext₀ <;> rfl)
    exact eq_of_heq (CategoryTheory.Functor.hcongr_hom he (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
  · intro x y f g
    have he := ha (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g)
      (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
    exact (congrArg (fun a => a.obj 0) he).symm

lemma edgeThin_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (ht : EdgeThin Y) : EdgeThin X := by
  intro s t h
  apply (CategoryTheory.mono_iff_injective (f.app (op ⦋1⦌))).mp inferInstance
  apply ht
  intro i
  simpa! only [SSet.δ_naturality_apply] using congrArg (f.app (op ⦋0⦌)) (h i)

lemma edgeAntisym_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (ha : EdgeAntisym Y) : EdgeAntisym X := by
  intro s t h₀ h₁
  have he := ha (f.app _ s) (f.app _ t)
    (by simpa! only [SSet.δ_naturality_apply] using congrArg (f.app (op ⦋0⦌)) h₀)
    (by simpa! only [SSet.δ_naturality_apply] using congrArg (f.app (op ⦋0⦌)) h₁)
  apply (CategoryTheory.mono_iff_injective (f.app (op ⦋0⦌))).mp inferInstance
  simpa! only [SSet.δ_naturality_apply] using he

variable {J : Type v} [Category.{w} J] [IsFiltered J]
variable {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
include hc

lemma eq_eventually {i : J} (s t : (F.obj i) _⦋0⦌)
    (h : (c.ι.app i).app _ s = (c.ι.app i).app _ t) :
    ∃ (j : J) (f : i ⟶ j), (F.map f).app _ s = (F.map f).app _ t :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋0⦌)) hc) s t).mp h

lemma edgeThin_colimit (ht : ∀ j, EdgeThin (F.obj j)) : EdgeThin c.pt := by
  intro s t he
  obtain ⟨i,s',t',hs,ht'⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋1⦌)) hc) s t
  change (c.ι.app i).app _ s' = s at hs
  change (c.ι.app i).app _ t' = t at ht'
  subst s; subst t
  obtain ⟨j,f,h₀⟩ := eq_eventually hc ((F.obj i).δ 0 s') ((F.obj i).δ 0 t') (by
    simp only [SSet.δ_naturality_apply]
    exact he 0)
  have h₁ : (c.ι.app j).app _ ((F.obj j).δ 1 ((F.map f).app _ s')) =
      (c.ι.app j).app _ ((F.obj j).δ 1 ((F.map f).app _ t')) := by
    have hn (x : (F.obj i) _⦋1⦌) :
        (c.ι.app j).app _ ((F.map f).app _ x) = (c.ι.app i).app _ x :=
      congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌) x) (c.w f)
    simp only [SSet.δ_naturality_apply,hn]
    exact he 1
  obtain ⟨k,g,h₁⟩ := eq_eventually hc _ _ h₁
  have hst : (F.map (f ≫ g)).app _ s' = (F.map (f ≫ g)).app _ t' := by
    apply ht k
    intro l
    fin_cases l
    · have hh := congrArg ((F.map g).app (op ⦋0⦌)) h₀
      simp only [SSet.δ_naturality_apply] at hh
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact hh
    · simp only [SSet.δ_naturality_apply] at h₁
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact h₁
  have hh := congrArg ((c.ι.app k).app (op ⦋1⦌)) hst
  have hn := congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌)) (c.w (f ≫ g))
  simp only [← types_comp_apply,← NatTrans.comp_app,hn] at hh
  exact hh

lemma edgeAntisym_colimit (ha : ∀ j, EdgeAntisym (F.obj j)) : EdgeAntisym c.pt := by
  intro s t he₀ he₁
  obtain ⟨i,s',t',hs,ht'⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋1⦌)) hc) s t
  change (c.ι.app i).app _ s' = s at hs
  change (c.ι.app i).app _ t' = t at ht'
  subst s; subst t
  obtain ⟨j,f,h₀⟩ := eq_eventually hc ((F.obj i).δ 0 s') ((F.obj i).δ 1 t') (by
    simp only [SSet.δ_naturality_apply]
    exact he₀)
  have h₁ : (c.ι.app j).app _ ((F.obj j).δ 1 ((F.map f).app _ s')) =
      (c.ι.app j).app _ ((F.obj j).δ 0 ((F.map f).app _ t')) := by
    have hn (x : (F.obj i) _⦋1⦌) :
        (c.ι.app j).app _ ((F.map f).app _ x) = (c.ι.app i).app _ x :=
      congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌) x) (c.w f)
    simp only [SSet.δ_naturality_apply,hn]
    exact he₁
  obtain ⟨k,g,h₁⟩ := eq_eventually hc _ _ h₁
  have hst : (F.obj k).δ 0 ((F.map (f ≫ g)).app _ s') =
      (F.obj k).δ 1 ((F.map (f ≫ g)).app _ s') := by
    apply ha k _ ((F.map (f ≫ g)).app _ t')
    · have hh := congrArg ((F.map g).app (op ⦋0⦌)) h₀
      simp only [SSet.δ_naturality_apply] at hh
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact hh
    · simp only [SSet.δ_naturality_apply] at h₁
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact h₁
  have hh := congrArg ((c.ι.app k).app (op ⦋0⦌)) hst
  have hn (x : (F.obj i) _⦋1⦌) :
      (c.ι.app k).app _ ((F.map (f ≫ g)).app _ x) = (c.ι.app i).app _ x :=
    congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌) x) (c.w (f ≫ g))
  simp only [SSet.δ_naturality_apply,hn] at hh
  exact hh

end Thomason.GeometricRecognition.Posetal

end

end OAI

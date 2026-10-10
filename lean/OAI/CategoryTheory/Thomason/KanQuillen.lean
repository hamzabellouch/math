import Mathlib
import OAI.CategoryTheory.Thomason.FiberRecognition

namespace OAI

/-! Kan Quillen. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition

lemma strictFiber_isPullback {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌) :
    IsPullback (strictFiber p y).ι (terminal.from (strictFiber p y : SSet)) p
      (SSet.const (X := ⊤_ SSet.{u}) y) := by
  have hw : (strictFiber p y).ι ≫ p = terminal.from (strictFiber p y : SSet) ≫ SSet.const y := by
    rw [strictFiber_ι_comp,SSet.comp_const]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk hw
    (fun s => strictFiberLift p y s.fst (by rw [s.condition,SSet.comp_const]))
    (fun s => strictFiberLift_ι _ _ _ _) (fun _ => Subsingleton.elim _ _) ?_
  intro s m hm _
  apply (cancel_mono (strictFiber p y).ι).mp
  rw [strictFiberLift_ι,hm]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition
open HornSubdivision Subdivision

lemma sequential_colimit_lifting {A B : SSet.{u}} [A.Finite] [B.Finite]
    (i : A ⟶ B) {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : ∀ n, HasLiftingProperty i (p.app n)) :
    HasLiftingProperty i (colim.map p) := by
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (op A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : PreservesFilteredColimitsOfSize.{0,0} (coyoneda.obj (op B)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  constructor
  intro a b sq
  obtain ⟨n,an,han⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit X) a
  obtain ⟨m,bm,hbm⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit Y) b
  change an ≫ colimit.ι X n = a at han
  change bm ≫ colimit.ι Y m = b at hbm
  have he : (an ≫ p.app n) ≫ colimit.ι Y n = (i ≫ bm) ≫ colimit.ι Y m := by
    rw [Category.assoc,← ι_colimMap,← Category.assoc,han,Category.assoc,hbm]
    exact sq.w
  obtain ⟨k,u,v,huv⟩ := exists_eq_of_preservesColimit_coyoneda (colimit.isColimit Y)
    (an ≫ p.app n) (i ≫ bm) he
  let := hp k
  let q : CommSq (an ≫ X.map u) i (p.app k) (bm ≫ Y.map v) :=
    ⟨by rw [Category.assoc,p.naturality,← Category.assoc]; exact huv⟩
  refine ⟨⟨{l := q.lift ≫ colimit.ι X k,fac_left := ?_,fac_right := ?_}⟩⟩
  · rw [← Category.assoc,q.fac_left,Category.assoc,colimit.w,han]
  · change (q.lift ≫ colimit.ι X k) ≫ colimMap p = b
    rw [Category.assoc,ι_colimMap,← Category.assoc,q.fac_right,Category.assoc,colimit.w,hbm]

lemma exStageMap_fibration {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p)
    (n : ℕ) : simplicialFibrations (exStageMap p n) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ex_preserves_fibrations _ ih

theorem exInfinity_fibration {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p) :
    simplicialFibrations (exInfinityFunctor.map p) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J,MorphismProperty.iSup_iff] at hi
  obtain ⟨n,⟨k⟩⟩ := hi
  apply sequential_colimit_lifting (SSet.horn (n+1) k).ι (exSequenceMap p)
  intro m
  exact exStageMap_fibration p hp m _ (by simp only [SSet.modelCategoryQuillen.J,MorphismProperty.iSup_iff]; exact ⟨n,⟨k⟩⟩)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition
open Subdivision

lemma weak_kan_fibration_rlp {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p) :
    SSet.modelCategoryQuillen.I.rlp p :=
  fibration_rlp_of_fibers p hp (weak_kan_fibration_fiber_rlp p hp hw)

theorem weak_fibration_rlp {K L : SSet.{u}} (p : K ⟶ L)
    (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p) :
    SSet.modelCategoryQuillen.I.rlp p := by
  let : SSet.KanComplex (exInfinityFunctor.obj K) := exInfinity_kan K
  let : SSet.KanComplex (exInfinityFunctor.obj L) := exInfinity_kan L
  have he : SSet.modelCategoryQuillen.I.rlp (exInfinityFunctor.map p) :=
    weak_kan_fibration_rlp _ (exInfinity_fibration p hp) ((exInfinity_map_weak_iff p).mpr hw)
  apply fibration_rlp_of_fibers p hp
  intro y
  let := strictFiber_kan p hp y
  apply weak_terminal_rlp
  apply (exInfinity_map_weak_iff (terminal.from (strictFiber p y : SSet))).mp
  apply KanQuillen.boundary_right_weak
  exact SSet.modelCategoryQuillen.I.rlp.of_isPullback
    ((strictFiber_isPullback p y).map exInfinityFunctor) he

theorem boundary_right_class : SSet.modelCategoryQuillen.I.rlp.{u} =
    simplicialFibrations ⊓ simplicialWeakEquivalences := by
  apply le_antisymm
  · intro K L p hp
    exact ⟨KanQuillen.boundary_right_fibrations p hp,KanQuillen.boundary_right_weak p hp⟩
  · intro K L p hp
    exact weak_fibration_rlp p hp.1 hp.2
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason.KanQuillen
open SSet.modelCategoryQuillen

lemma anodyne_class : SSet.anodyneExtensions.{u} =
    monomorphisms SSet ⊓ simplicialWeakEquivalences := by
  apply le_antisymm (le_inf anodyne_monomorphism anodyne_weak)
  intro X Y f hf
  let := horn_weakFactorization.{u}
  let d := factorizationData SSet.anodyneExtensions simplicialFibrations f
  have hpw : simplicialWeakEquivalences d.p :=
    simplicialWeakEquivalences.of_precomp d.i d.p (anodyne_weak _ d.hi) (d.fac.symm ▸ hf.2)
  have hp : I.rlp d.p := GeometricRecognition.weak_fibration_rlp d.p d.hp hpw
  have hf' : I.rlp.llp f := boundary_left_class.symm ▸ hf.1
  have : HasLiftingProperty f d.p := hf' d.p hp
  exact SSet.anodyneExtensions.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

lemma first_wfs : IsWeakFactorizationSystem
    (monomorphisms SSet.{u} ⊓ simplicialWeakEquivalences) simplicialFibrations := by
  rw [← anodyne_class]; exact horn_weakFactorization

lemma second_wfs : IsWeakFactorizationSystem
    (monomorphisms SSet.{u}) (simplicialFibrations ⊓ simplicialWeakEquivalences) := by
  rw [← GeometricRecognition.boundary_right_class]; exact boundary_weakFactorization

def geometricModel : KanQuillenModel.{u} := by
  letI : CategoryWithWeakEquivalences SSet.{u} := ⟨simplicialWeakEquivalences⟩
  letI : CategoryWithFibrations SSet.{u} := ⟨simplicialFibrations⟩
  letI : CategoryWithCofibrations SSet.{u} := ⟨monomorphisms SSet⟩
  letI : IsWeakFactorizationSystem (trivialCofibrations SSet.{u}) (fibrations SSet) := first_wfs
  letI : IsWeakFactorizationSystem (cofibrations SSet.{u}) (trivialFibrations SSet) := second_wfs
  letI : (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty :=
    simplicialWeakEquivalences_hasTwoOutOfThreeProperty
  exact ⟨ModelCategory.mk' SSet,rfl,rfl,rfl⟩
end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.DependentPosets
open CategoryTheory Limits Opposite
attribute [-instance] CategoryTheory.Sigma.sigma
variable {I : Type u} (P : I → Type u) [∀ i, PartialOrder (P i)]

def incl (i : I) : P i →o (Σ i, P i) where
  toFun := Sigma.mk i
  monotone' _ _ h := Sigma.LE.fiber _ _ _ h

def componentIso (i : I) : {x : Σ i, P i // x.1 = i} ≃o P i where
  toFun x := x.property ▸ x.val.2
  invFun x := ⟨⟨i,x⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,x⟩,h⟩; cases h; rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨⟨j,x⟩,hx⟩ ⟨⟨k,y⟩,hy⟩
    cases hx; cases hy
    exact Sigma.mk_le_mk_iff.symm

lemma label_const {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n)
    (j : Fin (n.unop.len+1)) : (s.obj j).1 = (s.obj 0).1 :=
  ((Sigma.le_def.mp (leOfHom (s.map (homOfLE (Fin.zero_le j))))).choose).symm

def restricted {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n) :
    Fin (n.unop.len+1) ⥤ {x : Σ i, P i // x.1 = (s.obj 0).1} where
  obj j := ⟨s.obj j, label_const P s j⟩
  map f := homOfLE (leOfHom (s.map f))

def branch {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n) :
    (nerve (P (s.obj 0).1)).obj n :=
  restricted P s ⋙ (componentIso P (s.obj 0).1).toOrderEmbedding.toOrderHom.toFunctor

lemma incl_branch {n : SimplexCategoryᵒᵖ} (s : (nerve (Σ i, P i)).obj n) :
    (nerveMap (incl P (s.obj 0).1).toFunctor).app n (branch P s) = s := by
  apply nerve.ext_of_isThin
  funext j
  change Sigma.mk (s.obj 0).1 ((label_const P s j) ▸ (s.obj j).2) = s.obj j
  exact Sigma.ext (label_const P s j).symm (eqRec_heq _ _)

def isColimit : IsColimit (Cofan.mk (nerve (Σ i, P i))
    (fun i => nerveMap (incl P i).toFunctor)) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj n)
    (fun i => nerve (P i)) (fun i => nerveMap (incl P i).toFunctor)).symm.toFun
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i = j := congrArg (fun s => (s.obj 0).1) h
    subst j
    have hxy : x = y := by
      apply nerve.ext_of_isThin
      funext k
      have hk := congrArg (fun s => s.obj k) h
      exact Sigma.mk.inj_iff.mp hk |>.2 |> eq_of_heq
    subst y
    rfl
  · intro s
    exact ⟨⟨(s.obj 0).1,branch P s⟩,incl_branch P s⟩

def iso : (∐ fun i => nerve (P i)) ≅ nerve (Σ i, P i) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (isColimit P)

@[reassoc] lemma iso_hom_ι (i : I) :
    Sigma.ι (fun i => nerve (P i)) i ≫ (iso P).hom = nerveMap (incl P i).toFunctor :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom (isColimit P) (Discrete.mk i)

variable {P}
def old (A : ∀ i, Set (P i)) : Set (Σ i, P i) := {x | x.2 ∈ A x.1}
lemma old_lower (A : ∀ i, Set (P i)) (hA : ∀ i, IsLowerSet (A i)) :
    IsLowerSet (old A) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h hy
  cases h with
  | fiber i x y h => exact hA i h hy

def oldIso (A : ∀ i, Set (P i)) : (Σ i, A i) ≃o old A where
  toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x := ⟨x.val.1,⟨x.val.2,x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    constructor
    · intro h
      change Sigma.LE ⟨i,x.val⟩ ⟨j,y.val⟩ at h
      obtain ⟨e,he⟩ := Sigma.le_def.mp h
      cases e
      exact Sigma.LE.fiber _ _ _ he
    · intro h
      cases h
      exact Sigma.LE.fiber _ _ _ (by assumption)

def oldNerveIso (A : ∀ i, Set (P i)) :
    (∐ fun i => nerve (A i)) ≅ nerve (old A) :=
  iso (fun i => A i) ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (Σ i, A i)) (β := PartOrd.of (old A)) (oldIso A))

@[reassoc] lemma oldNerveIso_ι (A : ∀ i, Set (P i)) (i : I) :
    Sigma.ι (fun i => nerve (A i)) i ≫ (oldNerveIso A).hom =
      nerveMap ((oldIso A).toOrderEmbedding.toOrderHom.comp (incl (fun i => A i) i)).toFunctor := by
  change Sigma.ι (fun i => nerve (A i)) i ≫
    ((iso (fun i => A i)).hom ≫
      nerveMap (oldIso A).toOrderEmbedding.toOrderHom.toFunctor) = _
  rw [iso_hom_ι_assoc]
  rfl

lemma old_naturality (A : ∀ i, Set (P i)) :
    Limits.Sigma.map (fun i => nerveMap (OrderEmbedding.subtype (A i)).toOrderHom.toFunctor) ≫
      (iso P).hom =
    (oldNerveIso A).hom ≫ nerveMap (OrderEmbedding.subtype (old A)).toOrderHom.toFunctor := by
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_map_assoc, iso_hom_ι]
  rw [← Category.assoc]
  erw [oldNerveIso_ι A i]
  rfl

open Attachments AttachmentComparison
lemma mem_upward_old (A : ∀ i, Set (P i)) (i : I) (x : P i) :
    (⟨i,x⟩ : Σ i, P i) ∈ upward (old A) ↔ x ∈ upward (A i) := by
  constructor
  · rintro ⟨⟨j,a⟩,ha,hax⟩
    obtain ⟨e,h⟩ := Sigma.le_def.mp hax
    cases e
    exact ⟨a,ha,h⟩
  · rintro ⟨a,ha,hax⟩
    exact ⟨⟨i,a⟩,ha,Sigma.LE.fiber _ _ _ hax⟩

def oldUp (A : ∀ i, Set (P i)) (z : upward (old A)) : upward (A z.val.1) :=
  ⟨z.val.2, (mem_upward_old A _ _).mp z.property⟩

def oldRetraction (A : ∀ i, Set (P i)) (r : ∀ i, upward (A i) →o A i) :
    upward (old A) →o old A where
  toFun z := ⟨⟨z.val.1,(r _ (oldUp A z)).val⟩,(r _ (oldUp A z)).property⟩
  monotone' := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ h
    obtain ⟨e,he⟩ := Sigma.le_def.mp h
    cases e
    exact Sigma.LE.fiber _ _ _ ((r i).monotone he)

lemma oldRetraction_retract (A : ∀ i, Set (P i)) (r : ∀ i, upward (A i) →o A i)
    (hr : ∀ i (a : A i), r i ⟨a.val,a.val,a.property,le_rfl⟩ = a) (a : old A) :
    oldRetraction A r ⟨a.val,a.val,a.property,le_rfl⟩ = a := by
  rcases a with ⟨⟨i,a⟩,ha⟩
  apply Subtype.ext
  change Sigma.mk i (r i _).val = Sigma.mk i a
  exact congrArg (fun x : A i => Sigma.mk i x.val) (hr i ⟨a,ha⟩)

lemma oldRetraction_adjunction (A : ∀ i, Set (P i)) (r : ∀ i, upward (A i) →o A i)
    (hadj : ∀ i (a : A i) (z : upward (A i)), a.val ≤ z.val ↔ a ≤ r i z)
    (a : old A) (z : upward (old A)) :
    a.val ≤ z.val ↔ a ≤ oldRetraction A r z := by
  rcases a with ⟨⟨i,a⟩,ha⟩
  rcases z with ⟨⟨j,z⟩,hz⟩
  constructor
  · intro h
    obtain ⟨e,he⟩ := Sigma.le_def.mp h
    cases e
    exact Sigma.LE.fiber _ _ _ ((hadj i ⟨a,ha⟩ _).mp he)
  · intro h
    obtain ⟨e,he⟩ := Sigma.le_def.mp h
    cases e
    exact Sigma.LE.fiber _ _ _ ((hadj i ⟨a,ha⟩ _).mpr he)
end Thomason.DependentPosets

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
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
  anodyne : SSet.anodyneExtensions
    (nerveMap (OrderEmbedding.toOrderHom (X := A) (Y := B)
      (OrderEmbedding.subtype A)).toFunctor)
attribute [instance] PosetAttachment.order

abbrev PosetAttachment.arrow (d : PosetAttachment.{u}) := Arrow.mk (inc 1 d.A)

def Admissible : MorphismProperty (OmegaCategory.NCategory.{u} 1) :=
  fun _ _ f => ∃ d : PosetAttachment.{u}, Nonempty (d.arrow ≅ Arrow.mk f)

instance : Admissible.{u}.RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    rintro _ _ e ⟨d,⟨a⟩⟩
    exact ⟨d,⟨a ≪≫ e⟩⟩)

lemma horn_admissible : hornImages (thomasonLeftFinite.{u} 1) ≤ Admissible := by
  rintro X Y f hf
  simp only [hornImages, MorphismProperty.iSup_iff] at hf
  obtain ⟨m,⟨k⟩⟩ := hf
  let d : PosetAttachment := {
    B := NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+2))))
    order := inferInstance
    A := oldSet (simplexFaces (SSet.horn (m+1) k))
    lower := oldSet_lower _
    retraction := flagRetraction _
    retract := flagRetraction_retract _
    adjunction := flagRetraction_adjunction _
    anodyne := by
      exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
        (oldFlagsIso (SSet.horn (m+1) k)) (Subdivision.sdTwiceSimplexIso (m+1))
        (oldFlagsIso_naturality (SSet.horn (m+1) k)).symm)).mp
          (HornSubdivision.sdTwice_horn_anodyne (by omega) k) }
  refine ⟨d, ⟨(Arrow.isoMk ((categorificationFinite 1).mapIso (oldFlagsIso (SSet.horn (m+1) k)))
    ((categorificationFinite 1).mapIso (Subdivision.sdTwiceSimplexIso (m+1))) ?_).symm⟩⟩
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
  anodyne := by
    let h := SSet.anodyneExtensions.colimMap
      (Discrete.natTrans (F := Discrete.functor (fun i => nerve (d i).A))
        (G := Discrete.functor (fun i => nerve (d i).B))
        (fun i => nerveMap (OrderEmbedding.toOrderHom (X := (d i.as).A)
          (Y := (d i.as).B) (OrderEmbedding.subtype (d i.as).A)).toFunctor))
      (fun i => (d i.as).anodyne)
    exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
      (DependentPosets.oldNerveIso (fun i => (d i).A))
      (DependentPosets.iso (fun i => (d i).B))
      (DependentPosets.old_naturality (fun i => (d i).A)).symm)).mp h

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

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
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

lemma poset_attachment_local (d : PosetAttachment.{u})
    {X Y : OmegaCategory.NCategory.{u} 1} (a : posetObj 1 d.A ⟶ X)
    (j : X ⟶ Y) (v : posetObj 1 d.B ⟶ Y) (sc : IsPushout a (inc 1 d.A) j v) :
    Local (N.map j) ∧ Mono (N.map j) := by
  let b := N.map a
  let i := N.map (inc 1 d.A)
  let ss := IsPushout.of_hasPushout b i
  let F : pushout b i ⟶ N.obj Y := ss.desc (N.map j) (N.map v) (by
    rw [← N.map_comp, ← N.map_comp, sc.w])
  have hFX : pushout.inl b i ≫ F = N.map j := ss.inl_desc _ _ _
  have hFB : pushout.inr b i ≫ F = N.map v := ss.inr_desc _ _ _
  have hF := comparison_local_one d.A d.lower d.retraction d.retract d.adjunction a j v sc ss F hFX hFB
  have hi : SSet.anodyneExtensions i := by
    let f : nerve d.A ⟶ nerve d.B := nerveMap
      (OrderEmbedding.toOrderHom (X := d.A) (Y := d.B) (OrderEmbedding.subtype d.A)).toFunctor
    let ηA := η (nerve d.A)
    let ηB := η (nerve d.B)
    have : IsIso ηA := OneCat.oneUnitCatIso (Cat.of d.A)
    have : IsIso ηB := OneCat.oneUnitCatIso (Cat.of d.B)
    have hn : f ≫ ηB = ηA ≫ i := (categorificationFiniteAdjunction 1).unit.naturality f
    have he : i = inv ηA ≫ f ≫ ηB := by
      apply (cancel_epi ηA).mp
      rw [IsIso.hom_inv_id_assoc]
      exact hn.symm
    rw [he]
    exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
      (SSet.anodyneExtensions.comp_mem _ _ d.anodyne (SSet.anodyneExtensions.of_isIso _))
  refine ⟨?_,nerve_attachment_mono d.A d.lower a j v sc⟩
  rw [← hFX]
  exact local_comp (local_anodyne _ (SSet.anodyneExtensions.of_isPushout ss hi)) hF

lemma admissible_pushout {A B X Y : OmegaCategory.NCategory.{u} 1}
    (i : A ⟶ B) (hi : Admissible i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) : Local (N.map j) ∧ Mono (N.map j) := by
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
  exact poset_attachment_local d _ _ _ sq

lemma coproduct_horn_pushout {X Y : OmegaCategory.NCategory.{u} 1}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (hornImages (thomasonLeftFinite 1))).pushouts j) :
    Local (N.map j) ∧ Mono (N.map j) := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout i
    (Admissible.coproducts_le _ (MorphismProperty.coproducts_monotone horn_admissible _ hi))
    a j v sc

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory

def OneStatement : Prop :=
  (hornImages (thomasonLeftFinite.{u} 1)).rlp.llp ≤ thomasonWeakEquivalencesFinite 1
end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.TransferAcyclicity
open CategoryTheory Limits Opposite
open KanLocal SubdividedUnit

lemma sequential_horn_weak {X Y : OmegaCategory.NCategory.{u} 1} (f : X ⟶ Y)
    (h : (MorphismProperty.coproducts.{u} (hornImages (thomasonLeftFinite 1))).pushouts.TransfiniteCompositionOfShape ℕ f) : thomasonWeakEquivalencesFinite 1 f := by
  let G := h.F ⋙ N
  let F := (Functor.const ℕ).obj (G.obj 0)
  let a : F ⟶ G := {
    app n := G.map (homOfLE (Nat.zero_le n))
    naturality i j u := by
      change 𝟙 (G.obj 0) ≫ G.map _ = G.map _ ≫ G.map u
      rw [Category.id_comp, ← G.map_comp]
      rfl }
  have hG (n : ℕ) : Local (G.map (homOfLE (Nat.le_succ n))) ∧
      Mono (G.map (homOfLE (Nat.le_succ n))) :=
    coproduct_horn_pushout _ (h.map_mem n (by simp))
  have ha (n : ℕ) : Local (a.app n) := by
    induction n with
    | zero =>
      change Local (G.map (𝟙 0))
      rw [G.map_id]
      exact local_iso _
    | succ n ih =>
      have he : a.app (n+1) = a.app n ≫ G.map (homOfLE (Nat.le_succ n)) := by
        change G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp]
        rfl
      rw [he]
      exact local_comp ih (hG n).1
  have hl := local_colimit_nat F G a (fun n => by dsimp [F]; infer_instance)
    (fun n => (hG n).2) ha
  have hcF : IsColimit (constCocone ℕ (G.obj 0)) := isColimitConstCocone _ _
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcG : IsColimit (N.mapCocone { pt := Y, ι := h.incl }) :=
    isColimitOfPreserves N h.isColimit
  let eF : G.obj 0 ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj Y ≅ colimit G := hcG.coconePointUniqueUpToIso (colimit.isColimit G)
  have eFι : eF.hom = colimit.ι F 0 := by
    have he : (𝟙 (G.obj 0)) ≫ eF.hom = colimit.ι F 0 :=
      hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) 0
    simpa only [Category.id_comp] using he
  have eGι : colimit.ι G 0 ≫ eG.inv = N.map (h.incl.app 0) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit G) 0
  have he : N.map (h.incl.app 0) = eF.hom ≫ colim.map a ≫ eG.inv := by
    rw [eFι, ← Category.assoc, colimit.ι_map, Category.assoc, eGι]
    change _ = G.map (𝟙 0) ≫ _
    rw [G.map_id, Category.id_comp]
  apply (Subdivision.thomasonWeakFinite_iff_nerve f).mpr
  apply local_weak
  rw [← h.fac, N.map_comp]
  change Local (N.map h.isoBot.inv ≫ N.map (h.incl.app 0))
  rw [he]
  exact local_comp (local_iso _) (local_comp (local_iso _) (local_comp hl (local_iso _)))

theorem one : OneStatement.{u} := by
  unfold OneStatement
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]
  rintro X Y f ⟨A,B,g,r,⟨h⟩⟩
  exact (thomasonWeakEquivalencesFinite 1).of_retract r (sequential_horn_weak g h)

end Thomason.TransferAcyclicity

end

noncomputable section
universe u v w z


namespace Thomason.FirstTransferredWFS
open CategoryTheory

def OneStatement : Prop :=
  MorphismProperty.IsWeakFactorizationSystem
    (thomasonCofibrationsFinite.{u} 1 ⊓ thomasonWeakEquivalencesFinite 1)
    (thomasonFibrationsFinite 1)
end Thomason.FirstTransferredWFS

end

noncomputable section
universe u v w z


namespace Thomason.FirstTransferredWFS
open CategoryTheory MorphismProperty

lemma leftClass_one :
    (thomasonFibrationsFinite.{u} 1).llp =
      thomasonCofibrationsFinite 1 ⊓ thomasonWeakEquivalencesFinite 1 := by
  have hc : (thomasonFibrationsFinite.{u} 1).llp ≤ thomasonCofibrationsFinite 1 :=
    fun _ _ _ hi _ _ p hp => hi p hp.1
  have hw : (thomasonFibrationsFinite.{u} 1).llp ≤ thomasonWeakEquivalencesFinite 1 := by
    have h := TransferAcyclicity.one.{u}
    unfold TransferAcyclicity.OneStatement at h
    rwa [hornImages_rlp (thomasonFiniteAdjunction 1)] at h
  apply le_antisymm (le_inf hc hw)
  intro X Y f hf
  have := thomasonFibrationsFinite_weakFactorization.{u} 1
  let d := factorizationData (thomasonFibrationsFinite 1).llp (thomasonFibrationsFinite 1) f
  have hpw : thomasonWeakEquivalencesFinite 1 d.p :=
    (thomasonWeakEquivalencesFinite 1).of_precomp d.i d.p (hw _ d.hi) (d.fac.symm ▸ hf.2)
  have : HasLiftingProperty f d.p := hf.1 d.p ⟨d.hp,hpw⟩
  exact (thomasonFibrationsFinite 1).llp.of_retract
    (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

theorem one : OneStatement.{u} := by
  unfold OneStatement
  rw [← leftClass_one]
  exact thomasonFibrationsFinite_weakFactorization 1
end Thomason.FirstTransferredWFS

end

noncomputable section
universe u v w z
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace Thomason

lemma boundaryImages_right_class {C : Type v} [Category.{u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (boundaryImages L).rlp = simplicialFibrations.inverseImage R ⊓
      simplicialWeakEquivalences.inverseImage R := by
  rw [boundaryImages_rlp adj, GeometricRecognition.boundary_right_class]
  rfl

lemma transferred_second_wfs {C : Type v} [Category.{u} C]
    [IsLocallyPresentable.{u} C] [HasColimitsOfSize.{u,u} C]
    {L : SSet.{u} ⥤ C} {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    IsWeakFactorizationSystem
      (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R).llp
      (simplicialFibrations.inverseImage R ⊓ simplicialWeakEquivalences.inverseImage R) := by
  rw [← boundaryImages_right_class adj]
  exact boundaryImages_weakFactorization L

@[instance_reducible] def modelOne : ModelCategory (OmegaCategory.NCategory.{u} 1) := by
  letI : CategoryWithWeakEquivalences (OmegaCategory.NCategory.{u} 1) :=
    ⟨thomasonWeakEquivalencesFinite 1⟩
  letI : CategoryWithFibrations (OmegaCategory.NCategory.{u} 1) := ⟨thomasonFibrationsFinite 1⟩
  letI : CategoryWithCofibrations (OmegaCategory.NCategory.{u} 1) := ⟨thomasonCofibrationsFinite 1⟩
  letI : (weakEquivalences (OmegaCategory.NCategory.{u} 1)).HasTwoOutOfThreeProperty :=
    thomasonWeakEquivalencesFinite_hasTwoOutOfThreeProperty 1
  letI : IsWeakFactorizationSystem
      (trivialCofibrations (OmegaCategory.NCategory.{u} 1))
      (fibrations (OmegaCategory.NCategory.{u} 1)) := FirstTransferredWFS.one
  letI : IsWeakFactorizationSystem
      (cofibrations (OmegaCategory.NCategory.{u} 1))
      (trivialFibrations (OmegaCategory.NCategory.{u} 1)) :=
    transferred_second_wfs (thomasonFiniteAdjunction 1)
  exact ModelCategory.mk' _

lemma modelOne_weak : modelOne.{u}.categoryWithWeakEquivalences.weakEquivalences =
    thomasonWeakEquivalencesFinite 1 := rfl
lemma modelOne_fib : modelOne.{u}.categoryWithFibrations.fibrations =
    thomasonFibrationsFinite 1 := rfl
lemma modelOne_cof : modelOne.{u}.categoryWithCofibrations.cofibrations =
    thomasonCofibrationsFinite 1 := rfl

def ModelStructuresOneStatement : Prop :=
  Nonempty KanQuillenModel.{u} ∧
  ∃ m : ModelCategory (OmegaCategory.NCategory.{u} 1),
    m.categoryWithWeakEquivalences.weakEquivalences = thomasonWeakEquivalencesFinite 1 ∧
    m.categoryWithFibrations.fibrations = thomasonFibrationsFinite 1 ∧
    m.categoryWithCofibrations.cofibrations = thomasonCofibrationsFinite 1

theorem modelStructuresOne : ModelStructuresOneStatement.{u} :=
  ⟨⟨KanQuillen.geometricModel⟩, modelOne, rfl,rfl,rfl⟩
end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GeometricRecognition
open KanLocal KanHomotopy Subdivision
open SSet.modelCategoryQuillen

lemma weak_local {A B : SSet.{u}} (f : A ⟶ B) (hf : simplicialWeakEquivalences f) : Local f := by
  let := KanQuillen.horn_weakFactorization.{u}
  let d := MorphismProperty.factorizationData SSet.anodyneExtensions simplicialFibrations f
  have hpw : simplicialWeakEquivalences d.p :=
    simplicialWeakEquivalences.of_precomp d.i d.p (KanQuillen.anodyne_weak _ d.hi) (d.fac.symm ▸ hf)
  rw [← d.fac]
  exact local_comp (local_anodyne _ d.hi)
    (local_heq _ (heq_of_rlp _ (by rw [SSet.rlp_monomorphisms]; exact weak_fibration_rlp _ d.hp hpw)))

lemma weak_kan_heq {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (hf : simplicialWeakEquivalences f) : IsHomotopyEquivalence f := by
  let := KanQuillen.horn_weakFactorization.{u}
  let d := MorphismProperty.factorizationData SSet.anodyneExtensions simplicialFibrations f
  have hpw : simplicialWeakEquivalences d.p :=
    simplicialWeakEquivalences.of_precomp d.i d.p (KanQuillen.anodyne_weak _ d.hi) (d.fac.symm ▸ hf)
  let : HomotopicalAlgebra.Fibration d.p := by
    rw [HomotopicalAlgebra.fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]; exact d.hp
  let : SSet.KanComplex d.Z := HomotopicalAlgebra.isFibrant_of_fibration d.p
  rw [← d.fac]
  exact heq_comp (heq_anodyne _ d.hi) (heq_of_rlp _ (by rw [SSet.rlp_monomorphisms]; exact weak_fibration_rlp _ d.hp hpw))

theorem left_proper : LeftProperFor simplicialWeakEquivalences.{u}
    (MorphismProperty.monomorphisms SSet) := by
  intro A B X Y i f g j sq hi hf
  let : Mono i := hi
  exact local_weak _ (local_pushout sq.flip (weak_local _ hf))

theorem right_proper : RightProperFor simplicialWeakEquivalences.{u}
    simplicialFibrations := by
  intro A B X Y f g p q sq hq hp
  apply (exInfinity_map_weak_iff g).mp
  let : SSet.KanComplex (exInfinityFunctor.obj B) := exInfinity_kan B
  let : SSet.KanComplex (exInfinityFunctor.obj Y) := exInfinity_kan Y
  exact homotopy_equivalence_weak _ (pullback_heq (sq.map exInfinityFunctor)
    (weak_kan_heq _ ((exInfinity_map_weak_iff p).mpr hp)) (exInfinity_fibration q hq))
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z


namespace Thomason.QuillenCriterion
open CategoryTheory

def OneStatement : Prop := ∀ (K : SSet.{u}) (Y : OmegaCategory.NCategory.{u} 1)
    (f : (thomasonLeftFinite 1).obj K ⟶ Y),
  thomasonWeakEquivalencesFinite 1 f ↔
    simplicialWeakEquivalences ((thomasonFiniteAdjunction 1).homEquiv K Y f)
end Thomason.QuillenCriterion

end

noncomputable section
universe u v w z


namespace Thomason.QuillenCriterion
open CategoryTheory
open Subdivision
lemma sdEx_unit_weak (K : SSet.{u}) :
    simplicialWeakEquivalences (SSet.sdExAdjunction.unit.app K) := by
  have h := exComparison_weak K
  change simplicialWeakEquivalences
    (SSet.sdExAdjunction.unit.app K ≫ SSet.ex.map (lastVertex.app K)) at h
  exact simplicialWeakEquivalences.of_postcomp _ _
    ((ex_map_weak_iff _).mpr (lastVertex_weak K)) h

lemma sdExSquared_unit_weak (K : SSet.{u}) :
    simplicialWeakEquivalences
      ((SSet.sdExAdjunction.comp SSet.sdExAdjunction).unit.app K) := by
  change simplicialWeakEquivalences
    (SSet.sdExAdjunction.unit.app K ≫
      SSet.ex.map (SSet.sdExAdjunction.unit.app (SSet.sd.obj K)))
  exact simplicialWeakEquivalences.comp_mem _ _ (sdEx_unit_weak K)
    ((ex_map_weak_iff _).mpr (sdEx_unit_weak _))

lemma unit_one_weak (K : SSet.{u}) :
    simplicialWeakEquivalences ((thomasonFiniteAdjunction 1).unit.app K) := by
  change simplicialWeakEquivalences
    ((SSet.sdExAdjunction.comp SSet.sdExAdjunction).unit.app K ≫
      (SSet.ex ⋙ SSet.ex).map
        ((categorificationFiniteAdjunction 1).unit.app ((SSet.sd ⋙ SSet.sd).obj K)))
  exact simplicialWeakEquivalences.comp_mem _ _ (sdExSquared_unit_weak K)
    ((exSquared_map_weak_iff _).mpr (SubdividedUnit.one K))

theorem one : OneStatement.{u} := by
  intro K Y f
  change simplicialWeakEquivalences ((thomasonRightFinite 1).map f) ↔
    simplicialWeakEquivalences
      ((thomasonFiniteAdjunction 1).unit.app K ≫ (thomasonRightFinite 1).map f)
  constructor
  · exact simplicialWeakEquivalences.comp_mem _ _ (unit_one_weak K)
  · exact simplicialWeakEquivalences.of_precomp _ _ (unit_one_weak K)
end Thomason.QuillenCriterion

end

end OAI

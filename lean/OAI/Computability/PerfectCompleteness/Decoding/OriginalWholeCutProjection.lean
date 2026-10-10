import OAI.Computability.PerfectCompleteness.Decoding.ChildAssemblyProjection
import OAI.Computability.PerfectCompleteness.Decoding.CutGroupedProjectionLemmas
import OAI.Computability.PerfectCompleteness.Sampling.NumberedUniformCut

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem exterior_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot),
      (∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) →
      Exterior rows repeats p left = Exterior rows repeats p right := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro left right hs; rfl
      | step i p =>
          intro left right hs
          have hroot := OriginalScalarProjection.scalarExterior_eq repeats (.step i p) left right hs
          have hselected := ih p (childSlots left i) (childSlots right i)
            (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
          have hord :
              ((j : RecursiveSampler.OffPath i) → Arrays (childSlots left j.val) rows) =
                ((j : RecursiveSampler.OffPath i) → Arrays (childSlots right j.val) rows) :=
            congrArg (fun A : RecursiveSampler.OffPath i → Type => (j : RecursiveSampler.OffPath i) → A j)
              (funext (fun j => congrArg
                (fun ss : Slots branch n → Fin t → MixedSupport.Slot => Arrays ss rows)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs j)))
          exact congrArg₂ (fun A B : Type => A × B)
            (congrArg (fun A : Type => BucketSampler.Direction (rows (n + 1)) → A) hroot)
            (congrArg₂ (fun A B : Type => A × B) hselected hord)

def exteriorEquiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) :
    Exterior rows repeats p left ≃ Exterior rows repeats p right :=
  Equiv.cast (exterior_eq rows repeats p left right hs)

theorem exteriorEquiv_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s) :
    (OriginalWholeCutTape.exteriorLaw rows repeats p left).pushforward
        (exteriorEquiv rows repeats p left right hs) =
      OriginalWholeCutTape.exteriorLaw rows repeats p right := by
  unfold OriginalWholeCutTape.exteriorLaw
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (exteriorEquiv rows repeats p left right hs)

private theorem cast_exterior_parts {I J A A' B B' : Type} {C C' : J → Type}
    (ha : A = A') (hb : B = B') (hc : ∀ j, C j = C' j)
    (h : ((I → A) × (B × ((j : J) → C j))) = ((I → A') × (B' × ((j : J) → C' j))))
    (x : (I → A) × (B × ((j : J) → C j))) :
    cast h x = (fun i => cast ha (x.1 i), (cast hb x.2.1, fun j => cast (hc j) (x.2.2 j))) := by
  have hC : C = C' := funext hc
  cases ha
  cases hb
  cases hC
  rfl

theorem exteriorEquiv_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (left right : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (.step i p) s → left s = right s)
    (ext : Exterior rows repeats (.step i p) right) :
    exteriorEquiv rows repeats (.step i p) right left (fun s h => (hs s h).symm) ext =
      (fun bucket => cast
        (OriginalScalarProjection.scalarExterior_eq repeats (.step i p) right left
          (fun s h => (hs s h).symm)) (ext.1 bucket),
        (exteriorEquiv rows repeats p (childSlots right i) (childSlots left i)
          (fun s h => (hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
          fun j => cast (congrArg (fun ss => Arrays ss rows)
            (WholeCutExteriorTransport.ordinarySlots_eq i p right left
              (fun s h => (hs s h).symm) j)) (ext.2.2 j))) :=
  cast_exterior_parts _ _ _ _ ext

private theorem reconstruct_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : Exterior rows repeats (.step i p) slots)
    (values : Values rows repeats (.step i p) slots)
    (below : BelowArrays rows (.step i p) slots) :
    reconstruct rows repeats (.step i p) slots ext values below (.inl ()) =
      reconstructBuckets rows repeats (.step i p) slots
        (fun bucket terminal => values (.inl (bucket, terminal))) ext.1 := rfl

private theorem reconstruct_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : Exterior rows repeats (.step i p) slots)
    (values : Values rows repeats (.step i p) slots)
    (below : BelowArrays rows (.step i p) slots) (node : Nodes branch n) :
    reconstruct rows repeats (.step i p) slots ext values below (.inr (i, node)) =
      reconstruct rows repeats p (childSlots slots i) ext.2.1
        (fun call => values (.inr call)) below node := by
  exact congrFun (WholeArraySampler.childrenAt_selected slots rows i
    (reconstruct rows repeats p (childSlots slots i) ext.2.1
      (fun call => values (.inr call)) below) ext.2.2) node

private theorem reconstruct_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : Exterior rows repeats (.step i p) slots)
    (values : Values rows repeats (.step i p) slots)
    (below : BelowArrays rows (.step i p) slots)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    reconstruct rows repeats (.step i p) slots ext values below (.inr (j.val, node)) =
      ext.2.2 j node := by
  exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
    (reconstruct rows repeats p (childSlots slots i) ext.2.1
      (fun call => values (.inr call)) below) ext.2.2 j) node

private theorem bucket_evaluate_pullback {ΩL ΩR : Type*} (width : Nat)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (evalL : ΩL → H left) (evalR : ΩR → H right)
    (tapeL : BucketSampler.Tape width ΩL) (tapeR : BucketSampler.Tape width ΩR)
    (heval : ∀ bucket x, (evalL (tapeL bucket)).val x =
      (evalR (tapeR bucket)).val (sourceProjection q x)) :
    BucketSampler.evaluate width evalL tapeL =
      fun row => HPullback q (BucketSampler.evaluate width evalR tapeR row) := by
  funext row
  apply Subtype.ext
  funext x
  exact (BucketSampler.evaluate_apply width (H left) evalL tapeL row x).trans
    ((Finset.sum_congr rfl (fun bucket _ =>
      congrArg (fun z : F2 => bucket.val row * z) (heval bucket x))).trans
        (BucketSampler.evaluate_apply width (H right) evalR tapeR row
          (sourceProjection q x)).symm)

theorem reconstruct_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_ : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (ext : Exterior rows repeats p right) (values : Values rows repeats p right)
      (below : BelowArrays rows p right),
    reconstruct rows repeats p left
        (exteriorEquiv rows repeats p right left (fun s h => (hs s h).symm) ext)
        (fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call))
        (fun child => ChildBlockProjection.arraysPullback rows
          (ChildAssemblyProjection.childProjection (CutGroupedProjection.cutProjection p q) child)
          (below child)) =
      ChildBlockProjection.arraysPullback rows q (reconstruct rows repeats p right ext values below) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk ext values below
          funext node row
          rcases node with u | ⟨child, node⟩
          · cases u
            change BucketSampler.evaluate (rows (n + 1)) id
                (fun a => HPullback q (values a)) row =
              HPullback q (BucketSampler.evaluate (rows (n + 1)) id values row)
            simp only [BucketSampler.evaluate, id_eq, map_sum, map_smul]
            rfl
          · rfl
      | step i p =>
          intro left right q hs hk ext values below
          let leftValues : Values rows repeats (.step i p) left :=
            fun call => HPullback (CutGroupedProjection.cutProjection (.step i p) q) (values call)
          let leftBelow : BelowArrays rows (.step i p) left :=
            fun child => ChildBlockProjection.arraysPullback rows
              (ChildAssemblyProjection.childProjection (CutGroupedProjection.cutProjection (.step i p) q) child)
              (below child)
          let leftExterior : Exterior rows repeats (.step i p) left :=
            (fun bucket => cast
              (OriginalScalarProjection.scalarExterior_eq repeats (.step i p) right left
                (fun s h => (hs s h).symm)) (ext.1 bucket),
              (exteriorEquiv rows repeats p (childSlots right i) (childSlots left i)
                (fun s h => (hs (i, s)
                  (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
                fun j => cast (congrArg (fun ss => Arrays ss rows)
                  (WholeCutExteriorTransport.ordinarySlots_eq i p right left
                    (fun s h => (hs s h).symm) j)) (ext.2.2 j)))
          have hext : exteriorEquiv rows repeats (.step i p) right left
              (fun s h => (hs s h).symm) ext = leftExterior :=
            exteriorEquiv_step rows repeats i p left right hs ext
          refine (congrArg (fun e : Exterior rows repeats (.step i p) left =>
            reconstruct rows repeats (.step i p) left e leftValues leftBelow) hext).trans ?_
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            have hrootL := reconstruct_root rows repeats i p left leftExterior leftValues leftBelow
            have hrootR := reconstruct_root rows repeats i p right ext values below
            have hbucket := bucket_evaluate_pullback (rows (n + 1)) left right q
              (id : H left → H left) (id : H right → H right)
              (fun bucket => OriginalScalarReconstruction.reconstruct F2 repeats (.step i p)
                (LeafDomain left) (fun terminal => leftValues (.inl (bucket, terminal)))
                (leftExterior.1 bucket))
              (fun bucket => OriginalScalarReconstruction.reconstruct F2 repeats (.step i p)
                (LeafDomain right) (fun terminal => values (.inl (bucket, terminal))) (ext.1 bucket))
              (fun bucket x => OriginalScalarProjection.reconstruct_pullback_apply repeats (.step i p)
                left right q hs hk
                (fun terminal => values (.inl (bucket, terminal))) (ext.1 bucket) x)
            exact congrFun (hrootL.trans (hbucket.trans
              (congrArg (fun f : Fin (rows (n + 1)) → H right =>
                fun r => HPullback q (f r)) hrootR).symm)) row
          · by_cases hji : j = i
            · subst j
              have hnodeL := congrFun
                (reconstruct_selected rows repeats i p left leftExterior leftValues leftBelow node) row
              have hnodeR := congrFun
                (reconstruct_selected rows repeats i p right ext values below node) row
              have hchild := congrFun (congrFun
                (ih p (childSlots left i) (childSlots right i) (fun s k => q (i, s) k)
                  (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                  (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                  ext.2.1 (fun call => values (.inr call)) below) node) row
              exact hnodeL.trans (hchild.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (i, node))))
                  hnodeR).symm)
            · have hnodeL := congrFun
                (reconstruct_ordinary rows repeats i p left leftExterior leftValues leftBelow ⟨j, hji⟩ node) row
              have hnodeR := congrFun
                (reconstruct_ordinary rows repeats i p right ext values below ⟨j, hji⟩ node) row
              have hcast := CutProjectionGeometry.arraysPullback_eq_cast rows
                (childSlots left j) (childSlots right j) (fun s k => q (j, s) k)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs ⟨j, hji⟩)
                (fun s k => hk (j, s) (WholeCutExteriorTransport.outside_ordinary i p ⟨j, hji⟩ s) k)
                (ext.2.2 ⟨j, hji⟩)
              have hcastRow := congrFun (congrFun hcast.symm node) row
              exact hnodeL.trans (hcastRow.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (j, node))))
                  hnodeR).symm)

theorem reconstruct_numbered_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCutBridge.NumberedRecord rows repeats p right) :
    OriginalWholeCutBridge.reconstruct rows repeats p left
        (exteriorEquiv rows repeats p right left (fun s h => (hs s h).symm) record.1,
          ChildAssemblyProjection.assembledPullback rows (CutGroupedProjection.cutProjection p q) record.2) =
      ChildBlockProjection.arraysPullback rows q
        (OriginalWholeCutBridge.reconstruct rows repeats p right record) :=
  reconstruct_pullback rows repeats p left right q hs hk record.1
    (fun call => record.2.1 (callNumbering rows repeats p call)) record.2.2

theorem fixed_projected_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k))) :
    ((OriginalWholeCutTape.exteriorLaw rows repeats p left).product
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p right) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows (CutGroupedProjection.cutProjection p q)))).pushforward
            (OriginalWholeCutBridge.reconstruct rows repeats p left) =
      (WholeArraySampler.law rows repeats p right).pushforward (ChildBlockProjection.arraysPullback rows q) := by
  rw [← exteriorEquiv_law rows repeats p right left (fun s h => (hs s h).symm),
    ← FiniteDistribution.product_pushforward
      (OriginalWholeCutTape.exteriorLaw rows repeats p right)
      (FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p right) rows))
      (exteriorEquiv rows repeats p right left (fun s h => (hs s h).symm))
      (ChildAssemblyProjection.assembledPullback rows (CutGroupedProjection.cutProjection p q)),
    FiniteDistribution.pushforward_comp]
  have hmap :
      (fun record : OriginalWholeCutBridge.NumberedRecord rows repeats p right =>
        OriginalWholeCutBridge.reconstruct rows repeats p left
          (exteriorEquiv rows repeats p right left (fun s h => (hs s h).symm) record.1,
            ChildAssemblyProjection.assembledPullback rows (CutGroupedProjection.cutProjection p q) record.2)) =
      (fun record => ChildBlockProjection.arraysPullback rows q
        (OriginalWholeCutBridge.reconstruct rows repeats p right record)) :=
    funext (reconstruct_numbered_pullback rows repeats p left right q hs hk)
  rw [hmap, ← FiniteDistribution.pushforward_comp,
    NumberedUniformCut.reconstruct_product_uniform]

end
end PerfectCompleteness.OriginalWholeCutProjection

end

end OAI

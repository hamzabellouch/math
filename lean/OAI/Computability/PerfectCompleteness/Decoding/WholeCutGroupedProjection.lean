import OAI.Computability.PerfectCompleteness.Decoding.CutGroupedProjectionLemmas
import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionAssembly
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplay

namespace OAI

section

namespace PerfectCompleteness.WholeCutGroupedProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def evaluateGrouped (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats p slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p slots) rows) : Arrays slots rows :=
  WholeCutSampler.evaluate rows repeats p slots
    ((WholeCutGrouping.splitTape rows repeats p slots).symm (ext, children))

theorem evaluateGrouped_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats (.step i p))
      (WholeCutGrouping.cutSlots (.step i p) slots) rows) :
    evaluateGrouped rows repeats (.step i p) slots ext children (.inl ()) =
      BucketSampler.evaluate (rows (n + 1))
        (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots))
        (fun bucket => (CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain slots)).symm
          (fun terminal child => (children child).1 (.inl (bucket, terminal)), ext.1 bucket)) := rfl

theorem evaluateGrouped_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats (.step i p))
      (WholeCutGrouping.cutSlots (.step i p) slots) rows) (node : Nodes branch n) :
    evaluateGrouped rows repeats (.step i p) slots ext children (.inr (i, node)) =
      evaluateGrouped rows repeats p (childSlots slots i) ext.2.1
        (fun child => (fun call => (children child).1 (.inr call), (children child).2)) node :=
  WholeArraySampler.evaluate_selected rows repeats i p slots
    (WholeCutSampler.collapse rows repeats (.step i p) slots
      ((WholeCutGrouping.splitTape rows repeats (.step i p) slots).symm (ext, children))) node

theorem evaluateGrouped_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats (.step i p))
      (WholeCutGrouping.cutSlots (.step i p) slots) rows)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    evaluateGrouped rows repeats (.step i p) slots ext children (.inr (j.val, node)) =
      ext.2.2 j node :=
  WholeArraySampler.evaluate_ordinary rows repeats i p slots
    (WholeCutSampler.collapse rows repeats (.step i p) slots
      ((WholeCutGrouping.splitTape rows repeats (.step i p) slots).symm (ext, children))) j node

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

theorem exterior_equiv_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (left right : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (.step i p) s → left s = right s)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) right) :
    WholeCutExteriorTransport.equiv rows repeats (.step i p) right left
        (fun s h => (hs s h).symm) ext =
      (fun bucket => cast
        (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) right left
          (fun s h => (hs s h).symm)) (ext.1 bucket),
        (WholeCutExteriorTransport.equiv rows repeats p (childSlots right i) (childSlots left i)
          (fun s h => (hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
          fun j => cast (congrArg (fun ss => Arrays ss rows)
            (WholeCutExteriorTransport.ordinarySlots_eq i p right left
              (fun s h => (hs s h).symm) j)) (ext.2.2 j))) :=
  cast_exterior_parts _ _ _ _ ext

private theorem assembleArrays_pullback (rows : Nat → Nat)
    (left right : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (data : CutChildGrouping.Assembled (C := Fin (rows (n + 1))) right rows) :
    WholeCutSampler.assembleArrays left rows (ChildAssemblyProjection.assembledPullback rows q data) =
      ChildBlockProjection.arraysPullback rows q (WholeCutSampler.assembleArrays right rows data) := by
  funext node row
  rcases node with u | ⟨i, node⟩ <;> rfl

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

theorem evaluateGrouped_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_ : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (ext : WholeCutGrouping.Exterior rows repeats p right)
      (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p right) rows),
    evaluateGrouped rows repeats p left
        (WholeCutExteriorTransport.equiv rows repeats p right left (fun s h => (hs s h).symm) ext)
        (ChildAssemblyProjection.rawPullback rows (CutGroupedProjection.cutProjection p q) children) =
      ChildBlockProjection.arraysPullback rows q
        (evaluateGrouped rows repeats p right ext children) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk ext children
          exact (congrArg (WholeCutSampler.assembleArrays left rows)
            (ChildAssemblyProjection.assemble_pullback (C := Fin (rows (n + 1)))
              rows q children)).trans
            (assembleArrays_pullback rows left right q
              (CutChildGrouping.assemble right rows children))
      | step i p =>
          intro left right q hs hk ext children
          let leftChildren := ChildAssemblyProjection.rawPullback rows
            (CutGroupedProjection.cutProjection (.step i p) q) children
          let leftExterior : WholeCutGrouping.Exterior rows repeats (.step i p) left :=
            (fun bucket => cast
              (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) right left
                (fun s h => (hs s h).symm)) (ext.1 bucket),
              (WholeCutExteriorTransport.equiv rows repeats p (childSlots right i) (childSlots left i)
                (fun s h => (hs (i, s)
                  (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
                fun j => cast (congrArg (fun ss => Arrays ss rows)
                  (WholeCutExteriorTransport.ordinarySlots_eq i p right left
                    (fun s h => (hs s h).symm) j)) (ext.2.2 j)))
          have hext : WholeCutExteriorTransport.equiv rows repeats (.step i p) right left
              (fun s h => (hs s h).symm) ext = leftExterior :=
            exterior_equiv_step rows repeats i p left right hs ext
          refine (congrArg
            (fun e : WholeCutGrouping.Exterior rows repeats (.step i p) left =>
              evaluateGrouped rows repeats (.step i p) left e leftChildren) hext).trans ?_
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            have hrootL := evaluateGrouped_root rows repeats i p left leftExterior leftChildren
            have hrootR := evaluateGrouped_root rows repeats i p right ext children
            have hbucket := bucket_evaluate_pullback (rows (n + 1)) left right q
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain left))
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain right))
              (fun bucket =>
                (CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain left)).symm
                  (fun terminal child => (leftChildren child).1 (.inl (bucket, terminal)),
                    leftExterior.1 bucket))
              (fun bucket =>
                (CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain right)).symm
                  (fun terminal child => (children child).1 (.inl (bucket, terminal)), ext.1 bucket))
              (fun bucket x => CutGroupedProjection.evaluate_rebuild repeats (.step i p)
                left right q hs hk
                (fun terminal child => (children child).1 (.inl (bucket, terminal))) (ext.1 bucket) x)
            exact congrFun (hrootL.trans (hbucket.trans
              (congrArg (fun f : Fin (rows (n + 1)) → H right =>
                fun r => HPullback q (f r)) hrootR).symm)) row
          · by_cases hji : j = i
            · subst j
              have hnodeL := congrFun
                (evaluateGrouped_selected rows repeats i p left leftExterior leftChildren node) row
              have hnodeR := congrFun
                (evaluateGrouped_selected rows repeats i p right ext children node) row
              have hchild := congrFun (congrFun
                (ih p (childSlots left i) (childSlots right i) (fun s k => q (i, s) k)
                  (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                  (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                  ext.2.1 (fun child => (fun call => (children child).1 (.inr call), (children child).2))) node) row
              exact hnodeL.trans (hchild.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (i, node))))
                  hnodeR).symm)
            · have hnodeL := congrFun
                (evaluateGrouped_ordinary rows repeats i p left leftExterior leftChildren ⟨j, hji⟩ node) row
              have hnodeR := congrFun
                (evaluateGrouped_ordinary rows repeats i p right ext children ⟨j, hji⟩ node) row
              have hcast := CutProjectionGeometry.arraysPullback_eq_cast rows
                (childSlots left j) (childSlots right j) (fun s k => q (j, s) k)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs ⟨j, hji⟩)
                (fun s k => hk (j, s) (WholeCutExteriorTransport.outside_ordinary i p ⟨j, hji⟩ s) k)
                (ext.2.2 ⟨j, hji⟩)
              have hcastRow := congrFun (congrFun hcast.symm node) row
              exact hnodeL.trans (hcastRow.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (j, node))))
                  hnodeR).symm)

theorem exteriorAt_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (placeholder left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external =
      WholeCutExteriorTransport.equiv rows repeats p
        (CutSlotAssembly.fill p outside right) (CutSlotAssembly.fill p outside left)
        (fun s h => (CutSlotAssembly.fill_outside_eq p outside left right s h).symm)
        (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external) := by
  apply eq_of_heq
  have hleft : HEq
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external) external :=
    cast_heq _ _
  have hright : HEq
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external) external :=
    cast_heq _ _
  exact hleft.trans ((cast_heq _ _).trans hright).symm

theorem fillChildren_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) right rows) :
    (fun i => CleanPhysicalReplay.fillChild rows repeats p outside left i
      ((ChildAssemblyProjection.rawPullback rows q children) i)) =
      ChildAssemblyProjection.rawPullback rows
        (CutGroupedProjection.cutProjection p
          (CutProjectionAssembly.fillProjection p outside left right q))
        (fun i => CleanPhysicalReplay.fillChild rows repeats p outside right i (children i)) := by
  funext i
  apply eq_of_heq
  exact (CleanPhysicalReplay.fillChild_heq rows repeats p outside left i
      ((ChildAssemblyProjection.rawPullback rows q children) i)).trans
    (CutProjectionGeometry.childPullback_heq rows
      (CleanPhysicalReplay.cutSlots_fill p outside left)
      (CleanPhysicalReplay.cutSlots_fill p outside right)
      (CutGroupedProjection.cutProjection p
        (CutProjectionAssembly.fillProjection p outside left right q)) q
      (CutProjectionAssembly.fillProjection_at_cut p outside left right q) i
      (CleanPhysicalReplay.fillChild rows repeats p outside right i (children i))
      (children i) (CleanPhysicalReplay.fillChild_heq rows repeats p outside right i
        (children i))).symm

theorem physicalTape_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (placeholder left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) right rows) :
    WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside left)
        (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder left external
          (ChildAssemblyProjection.rawPullback rows q children)) =
      ChildBlockProjection.arraysPullback rows
        (CutProjectionAssembly.fillProjection p outside left right q)
        (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside right)
          (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder right external children)) := by
  change evaluateGrouped rows repeats p (CutSlotAssembly.fill p outside left)
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external)
      (fun i => CleanPhysicalReplay.fillChild rows repeats p outside left i
        ((ChildAssemblyProjection.rawPullback rows q children) i)) =
    ChildBlockProjection.arraysPullback rows
      (CutProjectionAssembly.fillProjection p outside left right q)
      (evaluateGrouped rows repeats p (CutSlotAssembly.fill p outside right)
        (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external)
        (fun i => CleanPhysicalReplay.fillChild rows repeats p outside right i (children i)))
  rw [exteriorAt_pullback rows repeats p outside placeholder left right external,
    fillChildren_pullback]
  exact evaluateGrouped_pullback rows repeats p
    (CutSlotAssembly.fill p outside left) (CutSlotAssembly.fill p outside right)
    (CutProjectionAssembly.fillProjection p outside left right q)
    (CutSlotAssembly.fill_outside_eq p outside left right)
    (CutProjectionGeometry.fillProjection_outside p outside left right q)
    (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external)
    (fun i => CleanPhysicalReplay.fillChild rows repeats p outside right i (children i))

theorem fullJoint_physicalTape_pullback (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (placeholder left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) right rows)
    (x : Domain (CutSlotAssembly.fill p outside left)) :
    fullJoint (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside left)
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder left external
        (ChildAssemblyProjection.rawPullback rows q children))) x =
    fullJoint (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside right)
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder right external children))
      (sourceProjection (CutProjectionAssembly.fillProjection p outside left right q) x) := by
  rw [physicalTape_pullback]
  rfl

end
end PerfectCompleteness.WholeCutGroupedProjection

end

end OAI

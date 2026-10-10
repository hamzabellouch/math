import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayGroupingTransport

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayGroupingTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

export CutSamplerReplayGroupingTransport (outside_kept outside_eq retainedChildSlots_eq)

abbrev ChildBlock (C : Type) (rows : Nat → Nat)
    (slots : Slots branch m → Fin t → MixedSupport.Slot) :=
  (C → PointwiseSpaces.squareSpace (H slots)) × Arrays slots rows

def castChildren (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean) :
    WholeCutReplayGrouping.RetainedChildren rows repeats p target clean :=
  fun child => cast
    (congrArg (ChildBlock (WholeCutCalls.Index rows repeats p) rows)
      (retainedChildSlots_eq p slots target clean hs child)) (children child)

theorem castChildren_apply_heq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean)
    (child : {i : Fin (branch m) // ¬ clean i}) :
    HEq (castChildren rows repeats p slots target clean hs children child) (children child) :=
  cast_heq _ _

private theorem blockCast_calls {C : Type} (rows : Nat → Nat)
    {slots target : Slots branch m → Fin t → MixedSupport.Slot} (hs : slots = target)
    (x : ChildBlock C rows slots) (c : C) :
    (cast (congrArg (ChildBlock C rows) hs) x).1 c =
      cast (congrArg (fun ss => (PointwiseSpaces.squareSpace (H ss) : Type)) hs) (x.1 c) := by
  cases hs
  rfl

private theorem blockCast_arrays {C : Type} (rows : Nat → Nat)
    {slots target : Slots branch m → Fin t → MixedSupport.Slot} (hs : slots = target)
    (x : ChildBlock C rows slots) :
    (cast (congrArg (ChildBlock C rows) hs) x).2 =
      cast (congrArg (fun ss => Arrays ss rows) hs) x.2 := by
  cases hs
  rfl

theorem castChildren_calls (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean)
    (child : {i : Fin (branch m) // ¬ clean i}) (c : WholeCutCalls.Index rows repeats p) :
    (castChildren rows repeats p slots target clean hs children child).1 c =
      cast (congrArg (fun ss => (PointwiseSpaces.squareSpace (H ss) : Type))
        (retainedChildSlots_eq p slots target clean hs child)) ((children child).1 c) :=
  blockCast_calls rows (retainedChildSlots_eq p slots target clean hs child) (children child) c

theorem castChildren_arrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean)
    (child : {i : Fin (branch m) // ¬ clean i}) :
    (castChildren rows repeats p slots target clean hs children child).2 =
      cast (congrArg (fun ss => Arrays ss rows)
        (retainedChildSlots_eq p slots target clean hs child)) (children child).2 :=
  blockCast_arrays rows (retainedChildSlots_eq p slots target clean hs child) (children child)

private theorem blockCast_reindex {C D : Type} (rows : Nat → Nat) (f : D → C)
    {slots target : Slots branch m → Fin t → MixedSupport.Slot} (hs : slots = target)
    (x : ChildBlock C rows slots) :
    ((fun d => (cast (congrArg (ChildBlock C rows) hs) x).1 (f d)),
        (cast (congrArg (ChildBlock C rows) hs) x).2) =
      cast (congrArg (ChildBlock D rows) hs) (fun d => x.1 (f d), x.2) := by
  cases hs
  rfl

private theorem blockTransport_eq_cast {C : Type} (rows : Nat → Nat)
    (slots target : Slots branch m → Fin t → MixedSupport.Slot) (hs : slots = target)
    (x : ChildBlock C rows slots) :
    ((fun c => (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s)))).symm (x.1 c)),
      WholeCutReplayTransport.arraysTransport rows slots target
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s))) x.2) =
      cast (congrArg (ChildBlock C rows) hs) x := by
  cases hs
  apply Prod.ext
  · funext c
    apply Subtype.ext
    funext y
    rfl
  · funext node row
    apply Subtype.ext
    funext y
    rfl

private theorem arraysTransport_eq_cast (rows : Nat → Nat)
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (arrays : Arrays slots rows) :
    WholeCutReplayTransport.arraysTransport rows slots target
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s))) arrays =
      cast (congrArg (fun ss => Arrays ss rows) hs) arrays := by
  cases hs
  funext node row
  apply Subtype.ext
  funext y
  rfl

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
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf (.step i p) clean s → slots s = target s)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots) :
    WholeCutExteriorTransport.equiv rows repeats (.step i p) slots target
        (outside_eq (.step i p) slots target clean hs) ext =
      (fun bucket => cast
        (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
          (outside_eq (.step i p) slots target clean hs)) (ext.1 bucket),
        (WholeCutExteriorTransport.equiv rows repeats p (childSlots slots i) (childSlots target i)
          (outside_eq p (childSlots slots i) (childSlots target i) clean
            (fun s h => hs (i, s) (Or.inr h))) ext.2.1,
          fun j => cast (congrArg (fun ss => Arrays ss rows)
            (WholeCutExteriorTransport.ordinarySlots_eq i p slots target
              (outside_eq (.step i p) slots target clean hs) j)) (ext.2.2 j))) :=
  cast_exterior_parts _ _ _ _ ext

private theorem castChildren_tail (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf (.step i p) clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats (.step i p) slots clean) :
    (fun child =>
      (fun q => (castChildren rows repeats (.step i p) slots target clean hs children child).1 (.inr q),
        (castChildren rows repeats (.step i p) slots target clean hs children child).2)) =
      castChildren rows repeats p (childSlots slots i) (childSlots target i) clean
        (fun s h => hs (i, s) (Or.inr h))
        (fun child => (fun q => (children child).1 (.inr q), (children child).2)) := by
  funext child
  exact blockCast_reindex rows Sum.inr
    (retainedChildSlots_eq (.step i p) slots target clean hs child) (children child)

theorem transport_assemble (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (hs : ∀ s, keptLeaf p clean s → slots s = target s)
      (ext : WholeCutGrouping.Exterior rows repeats p slots)
      (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean),
    WholeCutReplayKeys.transportTape rows repeats p slots target clean hs
        (WholeCutReplayGrouping.assemble rows repeats p slots clean ext children) =
      WholeCutReplayGrouping.assemble rows repeats p target clean
        (WholeCutExteriorTransport.equiv rows repeats p slots target
          (outside_eq p slots target clean hs) ext)
        (castChildren rows repeats p slots target clean hs children) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots target clean hs ext children
          funext child
          exact blockTransport_eq_cast rows _ _
            (retainedChildSlots_eq (.refl (n + 1)) slots target clean hs child) (children child)
      | step i p =>
          intro slots target clean hs ext children
          rw [exterior_equiv_step rows repeats i p slots target clean hs ext]
          apply Prod.ext
          · funext bucket
            refine (CutSamplerReplayGroupingTransport.transport_assemble repeats (.step i p)
              slots target clean hs (ext.1 bucket)
              (fun terminal child => (children child).1 (.inl (bucket, terminal)))).trans ?_
            let exterior : CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain target) :=
              cast (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
                (outside_eq (.step i p) slots target clean hs)) (ext.1 bucket)
            change CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
                (LeafDomain target) clean exterior
                (CutSamplerReplayGroupingTransport.castTerminal repeats (.step i p)
                  slots target clean hs
                  (fun terminal child => (children child).1 (.inl (bucket, terminal)))) =
              CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
                (LeafDomain target) clean exterior
                (fun terminal child =>
                  (castChildren rows repeats (.step i p) slots target clean hs children child).1
                    (.inl (bucket, terminal)))
            apply congrArg (CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
              (LeafDomain target) clean exterior)
            funext terminal child
            exact (castChildren_calls rows repeats (.step i p) slots target clean hs
              children child (.inl (bucket, terminal))).symm
          · apply Prod.ext
            · refine (ih p (childSlots slots i) (childSlots target i) clean
                (fun s h => hs (i, s) (Or.inr h)) ext.2.1
                (fun child => (fun q => (children child).1 (.inr q), (children child).2))).trans ?_
              let exterior : WholeCutGrouping.Exterior rows repeats p (childSlots target i) :=
                WholeCutExteriorTransport.equiv rows repeats p (childSlots slots i) (childSlots target i)
                  (outside_eq p (childSlots slots i) (childSlots target i) clean
                    (fun s h => hs (i, s) (Or.inr h))) ext.2.1
              change WholeCutReplayGrouping.assemble rows repeats p (childSlots target i) clean exterior
                  (castChildren rows repeats p (childSlots slots i) (childSlots target i) clean
                    (fun s h => hs (i, s) (Or.inr h))
                    (fun child => (fun q => (children child).1 (.inr q), (children child).2))) =
                WholeCutReplayGrouping.assemble rows repeats p (childSlots target i) clean exterior
                  (fun child =>
                    (fun q => (castChildren rows repeats (.step i p) slots target clean hs
                      children child).1 (.inr q),
                      (castChildren rows repeats (.step i p) slots target clean hs children child).2))
              apply congrArg (WholeCutReplayGrouping.assemble rows repeats p
                (childSlots target i) clean exterior)
              exact (castChildren_tail rows repeats i p slots target clean hs children).symm
            · funext j
              exact arraysTransport_eq_cast rows _ _
                (WholeCutExteriorTransport.ordinarySlots_eq i p slots target
                  (outside_eq (.step i p) slots target clean hs) j) (ext.2.2 j)

theorem transportTape_target_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target target' : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s) (ht : target = target')
    (tape : WholeCutReplay.Tape rows repeats p slots clean) :
    cast (congrArg (fun ss => WholeCutReplay.Tape rows repeats p ss clean) ht)
        (WholeCutReplayKeys.transportTape rows repeats p slots target clean hs tape) =
      WholeCutReplayKeys.transportTape rows repeats p slots target' clean
        (fun s h => (hs s h).trans (congrFun ht s)) tape := by
  cases ht
  rfl

end
end PerfectCompleteness.WholeCutReplayGroupingTransport

end

end OAI

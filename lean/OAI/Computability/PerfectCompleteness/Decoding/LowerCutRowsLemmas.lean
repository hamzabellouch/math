import OAI.Computability.PerfectCompleteness.Decoding.LowerCutScalar
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutGrouping

namespace OAI

section

namespace PerfectCompleteness.LowerCutRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def reconstruct (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) : Arrays slots rows :=
  WholeCutSampler.evaluate rows repeats p slots
    ((splitTape rows repeats p slots).symm (exterior, raw))

theorem selectedRows_heq_upperNode (rows : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows),
      HEq (SelectedArrayReplacement.selectedRows rows p slots arrays)
        (arrays (WholeArrayInteriorExterior.upperNode p)) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots arrays; rfl
      | step i p =>
          intro slots arrays
          exact ih p (childSlots slots i) (fun node => arrays (.inr (i, node)))

theorem selectedRows_evaluate_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) :
    SelectedArrayReplacement.selectedRows rows (.step i p) slots
        (WholeCutSampler.evaluate rows repeats (.step i p) slots tape) =
      SelectedArrayReplacement.selectedRows rows p (childSlots slots i)
        (WholeCutSampler.evaluate rows repeats p (childSlots slots i) tape.2.1) := by
  rw [SelectedArrayReplacement.selectedRows_step]
  apply congrArg (SelectedArrayReplacement.selectedRows rows p (childSlots slots i))
  funext node
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_selected]
  rfl

theorem selectedRows_evaluate (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats p slots) (row : Fin (rows (m + 1))),
      SelectedArrayReplacement.selectedRows rows p slots
          (WholeCutSampler.evaluate rows repeats p slots tape) row =
        (CutChildGrouping.assemble (cutSlots p slots) rows
          ((splitTape rows repeats p slots tape).2)).1
            (WholeCutCalls.directRow rows repeats p row) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots tape row; rfl
      | step i p =>
          intro slots tape row
          rw [selectedRows_evaluate_step]
          exact ih p (childSlots slots i) tape.2.1 row

theorem selectedRows_reconstruct (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) (row : Fin (rows (m + 1))) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstruct rows repeats p slots exterior raw) row =
      (CutChildGrouping.assemble (cutSlots p slots) rows raw).1
        (WholeCutCalls.directRow rows repeats p row) := by
  unfold reconstruct
  rw [selectedRows_evaluate, Equiv.apply_symm_apply]

def selectRows (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p)
        (cutSlots p slots) rows →ₗ[F2]
      (Fin (rows (m + 1)) → H (cutSlots p slots)) where
  toFun x row := x.1 (WholeCutCalls.directRow rows repeats p row)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem selectRows_apply (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) (row : Fin (rows (m + 1))) :
    selectRows rows repeats p slots x row =
      x.1 (WholeCutCalls.directRow rows repeats p row) := rfl

theorem selectRows_surjective (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Function.Surjective (selectRows rows repeats p slots) := by
  intro fresh
  refine ⟨(Function.extend (WholeCutCalls.directRow rows repeats p) fresh (fun _ => 0),
    fun _ _ _ => 0), ?_⟩
  funext row
  exact (WholeCutCalls.directRow_injective rows repeats p).extend_apply fresh
    (fun _ => 0) row

theorem selectedRows_reconstruct_eq (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstruct rows repeats p slots exterior raw) =
      selectRows rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows raw) := by
  funext row
  exact selectedRows_reconstruct rows repeats p slots exterior raw row

end
end PerfectCompleteness.LowerCutRows

end

section

namespace PerfectCompleteness.LowerCutAssembled

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

abbrev Assembled (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p)
    (cutSlots p slots) rows

def reconstructBuckets (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : BucketSampler.Direction (rows n) →
      TerminalCalls.TerminalIndex repeats p → H (cutSlots p slots))
    (exterior : BucketSampler.Direction (rows n) →
      CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots)) :
    Fin (rows n) → H slots :=
  BucketSampler.evaluate (rows n) (id : H slots → H slots) (fun direction =>
    LowerCutScalar.reconstruct F2 repeats p (LeafDomain slots)
      (values direction) (exterior direction))

def reconstruct (rows repeats : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      Exterior rows repeats p slots → Assembled rows repeats p slots → Arrays slots rows
  | _, _, .refl _, slots, _, assembled =>
      WholeArraySampler.assemble slots rows assembled.1 assembled.2
  | _, _, .step i p, slots, exterior, assembled =>
      WholeArraySampler.assemble slots rows
        (reconstructBuckets rows repeats (.step i p) slots
          (fun direction terminal => assembled.1 (.inl (direction, terminal))) exterior.1)
        (WholeArraySampler.childrenAt slots rows i
          (reconstruct rows repeats p (childSlots slots i) exterior.2.1
            (fun call => assembled.1 (.inr call), assembled.2)) exterior.2.2)

theorem selectedRows_reconstruct (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots) (assembled : Assembled rows repeats p slots),
      SelectedArrayReplacement.selectedRows rows p slots
          (reconstruct rows repeats p slots exterior assembled) =
        LowerCutRows.selectRows rows repeats p slots assembled := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots exterior assembled; rfl
      | step i p =>
          intro slots exterior assembled
          rw [reconstruct, SelectedArrayReplacement.selectedRows_assemble_step]
          exact ih p (childSlots slots i) exterior.2.1
            (fun call => assembled.1 (.inr call), assembled.2)

theorem reconstruct_splitTape (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats p slots),
      reconstruct rows repeats p slots (splitTape rows repeats p slots tape).1
          (CutChildGrouping.assemble (cutSlots p slots) rows
            (splitTape rows repeats p slots tape).2) =
        WholeCutSampler.evaluate rows repeats p slots tape := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots tape; rfl
      | step i p =>
          intro slots tape
          apply congrArg₂ (WholeArraySampler.assemble slots rows)
          · apply congrArg (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots))
            funext direction
            exact LowerCutScalar.reconstruct_splitTape F2 repeats (.step i p)
              (LeafDomain slots) (tape.1 direction)
          · exact congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected tape.2.2)
              (ih p (childSlots slots i) tape.2.1)

theorem reconstruct_assemble (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) :
    reconstruct rows repeats p slots exterior
        (CutChildGrouping.assemble (cutSlots p slots) rows raw) =
      LowerCutRows.reconstruct rows repeats p slots exterior raw := by
  have h := reconstruct_splitTape rows repeats p slots
    ((splitTape rows repeats p slots).symm (exterior, raw))
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem reconstruct_congr_replace (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots)
      (x y : Assembled rows repeats p slots),
      (∀ call, (∀ row, call ≠ WholeCutCalls.directRow rows repeats p row) →
        y.1 call = x.1 call) → y.2 = x.2 →
      reconstruct rows repeats p slots exterior y =
        SelectedArrayReplacement.replace rows p slots
          (reconstruct rows repeats p slots exterior x)
          (LowerCutRows.selectRows rows repeats p slots y) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro slots exterior x y hcalls harrays
          change WholeArraySampler.assemble slots rows y.1 y.2 =
            WholeArraySampler.assemble slots rows y.1 x.2
          rw [harrays]
      | step i p =>
          intro slots exterior x y hcalls harrays
          simp only [reconstruct, SelectedArrayReplacement.replace_assemble_step]
          apply congrArg₂ (WholeArraySampler.assemble slots rows)
          · unfold reconstructBuckets
            apply congrArg (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots))
            funext direction
            apply congrArg (fun values => LowerCutScalar.reconstruct F2 repeats (.step i p)
              (LeafDomain slots) values (exterior.1 direction))
            funext terminal
            apply hcalls (.inl (direction, terminal))
            intro row h
            cases h
          · apply congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected exterior.2.2)
            apply ih p (childSlots slots i) exterior.2.1
              (fun call => x.1 (.inr call), x.2)
              (fun call => y.1 (.inr call), y.2)
            · intro call hcall
              apply hcalls (.inr call)
              intro row h
              exact hcall row (Sum.inr.inj h)
            · exact harrays

theorem reconstruct_congr_outside (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots) (x y : Assembled rows repeats p slots)
    (hcalls : ∀ call, (∀ row, call ≠ WholeCutCalls.directRow rows repeats p row) →
      y.1 call = x.1 call) (harrays : y.2 = x.2)
    (node : Nodes branch n) (hnode : node ≠ WholeArrayInteriorExterior.upperNode p) :
    reconstruct rows repeats p slots exterior y node =
      reconstruct rows repeats p slots exterior x node := by
  rw [reconstruct_congr_replace rows repeats p slots exterior x y hcalls harrays]
  exact SelectedArrayReplacement.replace_outside rows p slots
    (reconstruct rows repeats p slots exterior x)
    (LowerCutRows.selectRows rows repeats p slots y) node hnode

end
end PerfectCompleteness.LowerCutAssembled

end

section

namespace PerfectCompleteness.LowerCutCallSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))

abbrev OtherCall :=
  {q : WholeCutCalls.Index rows repeats p //
    ∀ row : Fin (rows (m + 1)), q ≠ WholeCutCalls.directRow rows repeats p row}

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

abbrev ChildArrays :=
  (i : Fin (branch m)) → Arrays (childSlots (cutSlots p slots) i) rows

abbrev Complement :=
  (OtherCall rows repeats p → H (cutSlots p slots)) × ChildArrays rows p slots

abbrev NativeRows := Fin (rows (m + 1)) → H (cutSlots p slots)

abbrev Assembled :=
  CutChildGrouping.Assembled (C := WholeCutCalls.Index rows repeats p) (cutSlots p slots) rows

instance complementFintype : Fintype (Complement rows repeats p slots) := Fintype.ofFinite _

def complement (x : Assembled rows repeats p slots) : Complement rows repeats p slots :=
  (fun q => x.1 q.val, x.2)

def splitAssembled : Assembled rows repeats p slots →ₗ[F2]
    Complement rows repeats p slots × NativeRows rows p slots where
  toFun x := (complement rows repeats p slots x, LowerCutRows.selectRows rows repeats p slots x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem splitAssembled_complement (x : Assembled rows repeats p slots) :
    (splitAssembled rows repeats p slots x).1 = complement rows repeats p slots x := rfl

@[simp] theorem splitAssembled_rows (x : Assembled rows repeats p slots) :
    (splitAssembled rows repeats p slots x).2 = LowerCutRows.selectRows rows repeats p slots x := rfl

@[simp] theorem complement_call (x : Assembled rows repeats p slots)
    (q : OtherCall rows repeats p) :
    (complement rows repeats p slots x).1 q = x.1 q.val := rfl

@[simp] theorem complement_arrays (x : Assembled rows repeats p slots) :
    (complement rows repeats p slots x).2 = x.2 := rfl

def merge (bg : Complement rows repeats p slots) (fresh : NativeRows rows p slots) :
    Assembled rows repeats p slots :=
  (fun q => if h : ∃ row, q = WholeCutCalls.directRow rows repeats p row then
      fresh (Classical.choose h)
    else bg.1 ⟨q, fun row hq => h ⟨row, hq⟩⟩,
   bg.2)

@[simp] theorem merge_directRow (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) (row : Fin (rows (m + 1))) :
    (merge rows repeats p slots bg fresh).1 (WholeCutCalls.directRow rows repeats p row) =
      fresh row := by
  have hex : ∃ j, WholeCutCalls.directRow rows repeats p row =
      WholeCutCalls.directRow rows repeats p j := ⟨row, rfl⟩
  change (if h : ∃ j, WholeCutCalls.directRow rows repeats p row =
      WholeCutCalls.directRow rows repeats p j then fresh (Classical.choose h) else _) = fresh row
  rw [dite_eq_left hex]
  apply congrArg fresh
  exact (WholeCutCalls.directRow_injective rows repeats p (Classical.choose_spec hex)).symm

@[simp] theorem merge_otherCall (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) (q : OtherCall rows repeats p) :
    (merge rows repeats p slots bg fresh).1 q.val = bg.1 q := by
  have hnot : ¬ ∃ row, q.val = WholeCutCalls.directRow rows repeats p row := by
    rintro ⟨row, hrow⟩
    exact q.property row hrow
  simp only [merge, dite_eq_right hnot]

@[simp] theorem merge_arrays (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    (merge rows repeats p slots bg fresh).2 = bg.2 := rfl

@[simp] theorem split_merge (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    splitAssembled rows repeats p slots (merge rows repeats p slots bg fresh) = (bg, fresh) := by
  apply Prod.ext
  · apply Prod.ext
    · funext q
      exact merge_otherCall rows repeats p slots bg fresh q
    · rfl
  · funext row
    exact merge_directRow rows repeats p slots bg fresh row

@[simp] theorem merge_split (x : Assembled rows repeats p slots) :
    merge rows repeats p slots (splitAssembled rows repeats p slots x).1
        (splitAssembled rows repeats p slots x).2 = x := by
  apply Prod.ext
  · funext q
    by_cases h : ∃ row, q = WholeCutCalls.directRow rows repeats p row
    · rcases h with ⟨row, rfl⟩
      exact merge_directRow rows repeats p slots _ _ row
    · exact merge_otherCall rows repeats p slots _ _ ⟨q, fun row hq => h ⟨row, hq⟩⟩
  · rfl

def splitEquiv : Assembled rows repeats p slots ≃ₗ[F2]
    Complement rows repeats p slots × NativeRows rows p slots where
  toFun := splitAssembled rows repeats p slots
  invFun z := merge rows repeats p slots z.1 z.2
  left_inv := merge_split rows repeats p slots
  right_inv z := split_merge rows repeats p slots z.1 z.2
  map_add' := (splitAssembled rows repeats p slots).map_add
  map_smul' := (splitAssembled rows repeats p slots).map_smul

@[simp] theorem splitEquiv_apply (x : Assembled rows repeats p slots) :
    splitEquiv rows repeats p slots x = splitAssembled rows repeats p slots x := rfl

@[simp] theorem splitEquiv_symm_apply
    (z : Complement rows repeats p slots × NativeRows rows p slots) :
    (splitEquiv rows repeats p slots).symm z = merge rows repeats p slots z.1 z.2 := rfl

theorem splitAssembled_surjective : Function.Surjective (splitAssembled rows repeats p slots) :=
  (splitEquiv rows repeats p slots).surjective

theorem splitAssembled_injective : Function.Injective (splitAssembled rows repeats p slots) :=
  (splitEquiv rows repeats p slots).injective

@[simp] theorem complement_merge (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    complement rows repeats p slots (merge rows repeats p slots bg fresh) = bg :=
  congrArg Prod.fst (split_merge rows repeats p slots bg fresh)

@[simp] theorem selectRows_merge (bg : Complement rows repeats p slots)
    (fresh : NativeRows rows p slots) :
    LowerCutRows.selectRows rows repeats p slots (merge rows repeats p slots bg fresh) = fresh :=
  congrArg Prod.snd (split_merge rows repeats p slots bg fresh)

theorem complement_eq_iff (x y : Assembled rows repeats p slots) :
    complement rows repeats p slots x = complement rows repeats p slots y ↔
      (∀ q : OtherCall rows repeats p, x.1 q.val = y.1 q.val) ∧ x.2 = y.2 := by
  constructor
  · intro h
    exact ⟨fun q => congrArg (fun z : Complement rows repeats p slots => z.1 q) h,
      congrArg (fun z : Complement rows repeats p slots => z.2) h⟩
  · rintro ⟨hcalls, harrays⟩
    exact Prod.ext (funext hcalls) harrays

end
end PerfectCompleteness.LowerCutCallSplit

end

end OAI

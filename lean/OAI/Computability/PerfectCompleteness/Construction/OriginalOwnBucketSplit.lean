import OAI.Computability.PerfectCompleteness.Algebra.HierarchicalMatrixTable
import OAI.Computability.PerfectCompleteness.Construction.OriginalCutBucketReplacement
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.OriginalWholeCutLaw

namespace OAI

section

namespace PerfectCompleteness.OriginalOwnBucketSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays TerminalCalls
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

@[instance_reducible] def valuesChildrenFintype (C : Type*) [Fintype C]
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    Fintype ((C → H slots) × ChildArrays rows slots) :=
  @instFintypeProd (C → H slots) (ChildArrays rows slots) inferInstance inferInstance

attribute [local instance 2000] valuesChildrenFintype

def OtherIndex (rows repeats : Nat → Nat) : {n m : Nat} → Path branch n m → Type
  | _, _, .refl _ => Empty
  | n + 1, _, .step i p =>
      (BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
        OtherIndex rows repeats p

instance otherIndexFintype (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype (OtherIndex rows repeats p) := by
  induction p with
  | refl m => exact inferInstanceAs (Fintype Empty)
  | @step n m i p ih =>
      letI : Fintype (OtherIndex rows repeats p) := ih
      exact inferInstanceAs (Fintype
        ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
          OtherIndex rows repeats p))

private def sumEmpty (A : Type*) : A ≃ A ⊕ Empty where
  toFun := Sum.inl
  invFun := Sum.elim id Empty.elim
  left_inv _ := rfl
  right_inv x := by
    cases x with
    | inl a => rfl
    | inr e => exact Empty.elim e

private def swapFirstSum (R A O : Type*) : R ⊕ (A ⊕ O) ≃ A ⊕ (R ⊕ O) where
  toFun
    | .inl r => .inr (.inl r)
    | .inr (.inl a) => .inl a
    | .inr (.inr o) => .inr (.inr o)
  invFun
    | .inl a => .inr (.inl a)
    | .inr (.inl r) => .inl r
    | .inr (.inr o) => .inr (.inr o)
  left_inv x := by rcases x with r | (a | o) <;> rfl
  right_inv x := by rcases x with a | (r | o) <;> rfl

def indexEquiv (rows repeats : Nat → Nat) : {n m : Nat} → (p : Path branch n m) →
    OriginalCutCalls.Index rows repeats p ≃
      BucketSampler.Direction (rows m) ⊕ OtherIndex rows repeats p
  | _, _, .refl _ => sumEmpty _
  | n + 1, _, .step i p =>
      (Equiv.sumCongr
        (Equiv.refl (BucketSampler.Direction (rows (n + 1)) ×
          TerminalIndex repeats (.step i p)))
        (indexEquiv rows repeats p)).trans (swapFirstSum _ _ _)

@[simp] theorem indexEquiv_ownBucket (rows repeats : Nat → Nat)
    (p : Path branch n m) (a : BucketSampler.Direction (rows m)) :
    indexEquiv rows repeats p (OriginalCutCalls.ownBucket rows repeats p a) = .inl a := by
  revert a
  induction p with
  | refl m => intro a; rfl
  | @step n m i p ih =>
      intro a
      change swapFirstSum _ _ _
        (.inr (indexEquiv rows repeats p (OriginalCutCalls.ownBucket rows repeats p a))) = _
      rw [ih a]
      rfl

@[simp] theorem indexEquiv_symm_inl (rows repeats : Nat → Nat)
    (p : Path branch n m) (a : BucketSampler.Direction (rows m)) :
    (indexEquiv rows repeats p).symm (.inl a) =
      OriginalCutCalls.ownBucket rows repeats p a := by
  apply (indexEquiv rows repeats p).injective
  rw [Equiv.apply_symm_apply, indexEquiv_ownBucket]

def otherCall (rows repeats : Nat → Nat) (p : Path branch n m)
    (call : OtherIndex rows repeats p) : OriginalCutCalls.Index rows repeats p :=
  (indexEquiv rows repeats p).symm (.inr call)

@[simp] theorem indexEquiv_otherCall (rows repeats : Nat → Nat)
    (p : Path branch n m) (call : OtherIndex rows repeats p) :
    indexEquiv rows repeats p (otherCall rows repeats p call) = .inr call :=
  (indexEquiv rows repeats p).apply_symm_apply (.inr call)

theorem otherCall_injective (rows repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (otherCall rows repeats p) := by
  intro a b h
  have h' := congrArg (indexEquiv rows repeats p) h
  simpa only [indexEquiv_otherCall, Sum.inr.injEq] using h'

theorem otherCall_ne_ownBucket (rows repeats : Nat → Nat) (p : Path branch n m)
    (call : OtherIndex rows repeats p) (a : BucketSampler.Direction (rows m)) :
    otherCall rows repeats p call ≠ OriginalCutCalls.ownBucket rows repeats p a := by
  intro h
  have h' := congrArg (indexEquiv rows repeats p) h
  rw [indexEquiv_otherCall, indexEquiv_ownBucket] at h'
  cases h'

def valuesEquiv (rows repeats : Nat → Nat) (p : Path branch n m) (A : Type*) :
    (OriginalCutCalls.Index rows repeats p → A) ≃
      (BucketSampler.Direction (rows m) → A) × (OtherIndex rows repeats p → A) :=
  (Equiv.arrowCongr (indexEquiv rows repeats p) (Equiv.refl A)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] theorem valuesEquiv_own (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (values : OriginalCutCalls.Index rows repeats p → A)
    (a : BucketSampler.Direction (rows m)) :
    (valuesEquiv rows repeats p A values).1 a =
      values (OriginalCutCalls.ownBucket rows repeats p a) := by
  change values ((indexEquiv rows repeats p).symm (.inl a)) = _
  rw [indexEquiv_symm_inl]

@[simp] theorem valuesEquiv_other (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (values : OriginalCutCalls.Index rows repeats p → A)
    (call : OtherIndex rows repeats p) :
    (valuesEquiv rows repeats p A values).2 call =
      values (otherCall rows repeats p call) := rfl

@[simp] theorem valuesEquiv_symm_own (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (own : BucketSampler.Direction (rows m) → A)
    (other : OtherIndex rows repeats p → A) (a : BucketSampler.Direction (rows m)) :
    (valuesEquiv rows repeats p A).symm (own, other)
        (OriginalCutCalls.ownBucket rows repeats p a) = own a := by
  have h := congrArg (fun z => z.1 a)
    ((valuesEquiv rows repeats p A).apply_symm_apply (own, other))
  simpa only [valuesEquiv_own] using h

@[simp] theorem valuesEquiv_symm_other (rows repeats : Nat → Nat) (p : Path branch n m)
    (A : Type*) (own : BucketSampler.Direction (rows m) → A)
    (other : OtherIndex rows repeats p → A) (call : OtherIndex rows repeats p) :
    (valuesEquiv rows repeats p A).symm (own, other)
        (otherCall rows repeats p call) = other call := by
  have h := congrArg (fun z => z.2 call)
    ((valuesEquiv rows repeats p A).apply_symm_apply (own, other))
  simpa only [valuesEquiv_other] using h

theorem valuesEquiv_law (rows repeats : Nat → Nat) (p : Path branch n m)
    {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    (FiniteProduct.law (fun _ : OriginalCutCalls.Index rows repeats p => μ)).pushforward
        (valuesEquiv rows repeats p A) =
      (FiniteProduct.law (fun _ : BucketSampler.Direction (rows m) => μ)).product
        (FiniteProduct.law (fun _ : OtherIndex rows repeats p => μ)) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change (∏ call : OriginalCutCalls.Index rows repeats p,
      μ.weight (Sum.elim z.1 z.2 (indexEquiv rows repeats p call))) =
    (∏ a : BucketSampler.Direction (rows m), μ.weight (z.1 a)) *
      ∏ other : OtherIndex rows repeats p, μ.weight (z.2 other)
  rw [(indexEquiv rows repeats p).prod_comp
    (fun tag => μ.weight (Sum.elim z.1 z.2 tag)), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

abbrev BucketTape (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots))

abbrev OtherValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OtherIndex rows repeats p → H (cutSlots p slots)

abbrev Complement (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  Exterior rows repeats p slots × (OtherValues rows repeats p slots × BelowArrays rows p slots)

def recordEquiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Record rows repeats p slots ≃ BucketTape rows p slots × Complement rows repeats p slots where
  toFun record :=
    ((valuesEquiv rows repeats p (H (cutSlots p slots)) record.2.1).1,
      (record.1,
        ((valuesEquiv rows repeats p (H (cutSlots p slots)) record.2.1).2, record.2.2)))
  invFun z :=
    (z.2.1, ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm (z.1, z.2.2.1),
      z.2.2.2))
  left_inv record := by
    rcases record with ⟨exterior, values, below⟩
    change (exterior, ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm
      (valuesEquiv rows repeats p (H (cutSlots p slots)) values), below)) = _
    rw [Equiv.symm_apply_apply]
  right_inv z := by
    rcases z with ⟨own, exterior, other, below⟩
    change
      (((valuesEquiv rows repeats p (H (cutSlots p slots)))
          ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm (own, other))).1,
        (exterior,
          (((valuesEquiv rows repeats p (H (cutSlots p slots)))
            ((valuesEquiv rows repeats p (H (cutSlots p slots))).symm (own, other))).2,
            below))) = _
    rw [Equiv.apply_symm_apply]

def assembleRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    Record rows repeats p slots :=
  (recordEquiv rows repeats p slots).symm (own, complement)

@[simp] theorem recordEquiv_own (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) (a : BucketSampler.Direction (rows (m + 1))) :
    (recordEquiv rows repeats p slots record).1 a =
      record.2.1 (OriginalCutCalls.ownBucket rows repeats p a) :=
  valuesEquiv_own rows repeats p (H (cutSlots p slots)) record.2.1 a

@[simp] theorem split_assembleRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    recordEquiv rows repeats p slots (assembleRecord rows repeats p slots own complement) =
      (own, complement) :=
  (recordEquiv rows repeats p slots).apply_symm_apply (own, complement)

@[simp] theorem assembleRecord_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) :
    assembleRecord rows repeats p slots (recordEquiv rows repeats p slots record).1
        (recordEquiv rows repeats p slots record).2 = record :=
  (recordEquiv rows repeats p slots).symm_apply_apply record

@[simp] theorem assembleRecord_exterior (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    (assembleRecord rows repeats p slots own complement).1 = complement.1 := rfl

@[simp] theorem assembleRecord_below (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    (assembleRecord rows repeats p slots own complement).2.2 = complement.2.2 := rfl

@[simp] theorem assembleRecord_own (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (assembleRecord rows repeats p slots own complement).2.1
        (OriginalCutCalls.ownBucket rows repeats p a) = own a :=
  valuesEquiv_symm_own rows repeats p (H (cutSlots p slots)) own complement.2.1 a

@[simp] theorem assembleRecord_other (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (call : OtherIndex rows repeats p) :
    (assembleRecord rows repeats p slots own complement).2.1 (otherCall rows repeats p call) =
      complement.2.1 call :=
  valuesEquiv_symm_other rows repeats p (H (cutSlots p slots)) own complement.2.1 call

theorem assembleRecord_nonown_eq (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own₁ own₂ : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (call : OriginalCutCalls.Index rows repeats p)
    (hcall : ∀ a, call ≠ OriginalCutCalls.ownBucket rows repeats p a) :
    (assembleRecord rows repeats p slots own₁ complement).2.1 call =
      (assembleRecord rows repeats p slots own₂ complement).2.1 call := by
  cases he : indexEquiv rows repeats p call with
  | inl a =>
      exfalso
      apply hcall a
      apply (indexEquiv rows repeats p).injective
      rw [indexEquiv_ownBucket]
      exact he
  | inr other =>
      have hc : call = otherCall rows repeats p other := by
        apply (indexEquiv rows repeats p).injective
        rw [indexEquiv_otherCall]
        exact he
      rw [hc, assembleRecord_other, assembleRecord_other]

def complementLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots)))
    (exterior : FiniteDistribution (Exterior rows repeats p slots))
    (below : FiniteDistribution (BelowArrays rows p slots)) :
    FiniteDistribution (Complement rows repeats p slots) :=
  exterior.product ((FiniteProduct.law
    (fun _ : OtherIndex rows repeats p => scalar)).product below)

theorem independent_record_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots)))
    (exterior : FiniteDistribution (Exterior rows repeats p slots))
    (below : FiniteDistribution (BelowArrays rows p slots)) :
    (exterior.product ((FiniteProduct.law
        (fun _ : OriginalCutCalls.Index rows repeats p => scalar)).product below)).pushforward
          (recordEquiv rows repeats p slots) =
      (BucketSampler.tapeLaw (rows (m + 1)) scalar).product
        (complementLaw rows repeats p slots scalar exterior below) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change exterior.weight z.2.1 *
      ((∏ call : OriginalCutCalls.Index rows repeats p,
        scalar.weight (Sum.elim z.1 z.2.2.1 (indexEquiv rows repeats p call))) *
          below.weight z.2.2.2) =
    (∏ a : BucketSampler.Direction (rows (m + 1)), scalar.weight (z.1 a)) *
      (exterior.weight z.2.1 *
        ((∏ other : OtherIndex rows repeats p, scalar.weight (z.2.2.1 other)) *
          below.weight z.2.2.2))
  rw [(indexEquiv rows repeats p).prod_comp
    (fun tag => scalar.weight (Sum.elim z.1 z.2.2.1 tag)), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

def actualComplementLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Complement rows repeats p slots) :=
  complementLaw rows repeats p slots
    (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (exteriorLaw rows repeats p slots)
    (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q (cutSlots p slots))

theorem recordLaw_split (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
        (recordEquiv rows repeats p slots) =
      (BucketSampler.tapeLaw (rows (m + 1))
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))).product
          (actualComplementLaw rows repeats p chosen q slots) :=
  independent_record_split rows repeats p slots
    (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (exteriorLaw rows repeats p slots)
    (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q (cutSlots p slots))

theorem uniform_record_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (recordEquiv rows repeats p slots) =
      (FiniteDistribution.uniform (BucketTape rows p slots)).product
        (FiniteDistribution.uniform (Complement rows repeats p slots)) := by
  rw [← FiniteDistribution.transport_eq_pushforward,
    UniformConditioning.uniform_transport, WholeCutSampler.uniform_product]

theorem uniform_record_split_bucketLaw (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (recordEquiv rows repeats p slots) =
      (BucketSampler.tapeLaw (rows (m + 1))
        (FiniteDistribution.uniform (H (cutSlots p slots)))).product
          (FiniteDistribution.uniform (Complement rows repeats p slots)) := by
  rw [BucketSampler.tapeLaw, UniformLinearImage.law_uniform]
  exact uniform_record_split rows repeats p slots

theorem uniform_assembleRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((FiniteDistribution.uniform (BucketTape rows p slots)).product
        (FiniteDistribution.uniform (Complement rows repeats p slots))).pushforward
          (fun z => assembleRecord rows repeats p slots z.1 z.2) =
      FiniteDistribution.uniform (Record rows repeats p slots) := by
  rw [WholeCutSampler.uniform_product]
  change (FiniteDistribution.uniform
    (BucketTape rows p slots × Complement rows repeats p slots)).pushforward
      (recordEquiv rows repeats p slots).symm = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (recordEquiv rows repeats p slots).symm

def zeroOwnReconstruction (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (complement : Complement rows repeats p slots) : Arrays slots rows :=
  reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots 0 complement)

theorem reconstruct_assembleRecord_outside (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own₁ own₂ : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (node : Nodes branch n) (hnode : node ≠ WholeArrayInteriorExterior.upperNode p) :
    reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots own₁ complement)
        node =
      reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots own₂ complement)
        node := by
  change reconstruct rows repeats p slots complement.1
      (assembleRecord rows repeats p slots own₁ complement).2.1 complement.2.2 node =
    reconstruct rows repeats p slots complement.1
      (assembleRecord rows repeats p slots own₂ complement).2.1 complement.2.2 node
  exact OriginalCutBucketReplacement.reconstruct_outside_eq_of_nonown_eq rows repeats p slots
    complement.1 _ _ complement.2.2
    (assembleRecord_nonown_eq rows repeats p slots own₁ own₂ complement) node hnode

def background (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (complement : Complement rows repeats p slots) :
    HierarchicalMatrixTable.Background (rows := rows) slots (WholeArrayInteriorExterior.upperNode p) :=
  HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
    (zeroOwnReconstruction rows repeats p slots complement)

theorem background_assembleRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots own complement)) =
      background rows repeats p slots complement := by
  funext node
  exact reconstruct_assembleRecord_outside rows repeats p slots own 0 complement node.val node.property

theorem background_record (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) :
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (reconstructRecord rows repeats p slots record) =
      background rows repeats p slots (recordEquiv rows repeats p slots record).2 := by
  have h := background_assembleRecord rows repeats p slots
    (recordEquiv rows repeats p slots record).1 (recordEquiv rows repeats p slots record).2
  rw [assembleRecord_split] at h
  exact h

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) := Fintype.ofFinite _

def backgroundLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) :=
  (FiniteDistribution.uniform (Complement rows repeats p slots)).pushforward
    (background rows repeats p slots)

def actualBackgroundLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) :=
  (actualComplementLaw rows repeats p chosen q slots).pushforward
    (background rows repeats p slots)

theorem recordLaw_own_background (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
        (fun record =>
          ((recordEquiv rows repeats p slots record).1,
            HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
              (reconstructRecord rows repeats p slots record))) =
      (BucketSampler.tapeLaw (rows (m + 1))
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))).product
          (actualBackgroundLaw rows repeats p chosen q slots) := by
  calc
    _ = ((OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
        (recordEquiv rows repeats p slots)).pushforward
          (fun z => (z.1, background rows repeats p slots z.2)) := by
      rw [FiniteDistribution.pushforward_comp]
      apply congrArg (OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
      funext record
      exact Prod.ext rfl (background_record rows repeats p slots record)
    _ = ((BucketSampler.tapeLaw (rows (m + 1))
        (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))).product
          (actualComplementLaw rows repeats p chosen q slots)).pushforward
            (fun z => (z.1, background rows repeats p slots z.2)) := by
      rw [recordLaw_split]
    _ = _ := by
      simpa only [id_eq, FiniteDistribution.pushforward_id, actualBackgroundLaw] using
        (FiniteDistribution.product_pushforward
          (BucketSampler.tapeLaw (rows (m + 1))
            (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))
          (actualComplementLaw rows repeats p chosen q slots)
          (id : BucketTape rows p slots → BucketTape rows p slots)
          (background rows repeats p slots))

theorem uniform_own_background (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (fun record =>
          ((recordEquiv rows repeats p slots record).1,
            HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
              (reconstructRecord rows repeats p slots record))) =
      (FiniteDistribution.uniform (BucketTape rows p slots)).product
        (backgroundLaw rows repeats p slots) := by
  calc
    _ = ((FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (recordEquiv rows repeats p slots)).pushforward
          (fun z => (z.1, background rows repeats p slots z.2)) := by
      rw [FiniteDistribution.pushforward_comp]
      apply congrArg ((FiniteDistribution.uniform (Record rows repeats p slots)).pushforward)
      funext record
      exact Prod.ext rfl (background_record rows repeats p slots record)
    _ = ((FiniteDistribution.uniform (BucketTape rows p slots)).product
        (FiniteDistribution.uniform (Complement rows repeats p slots))).pushforward
          (fun z => (z.1, background rows repeats p slots z.2)) := by
      rw [uniform_record_split]
    _ = _ := by
      simpa only [id_eq, FiniteDistribution.pushforward_id, backgroundLaw] using
        (FiniteDistribution.product_pushforward
          (FiniteDistribution.uniform (BucketTape rows p slots))
          (FiniteDistribution.uniform (Complement rows repeats p slots))
          (id : BucketTape rows p slots → BucketTape rows p slots)
          (background rows repeats p slots))

end
end PerfectCompleteness.OriginalOwnBucketSplit

end

end OAI

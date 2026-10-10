import OAI.Computability.PerfectCompleteness.Foundations.CanonicalPartialTable
import OAI.Computability.PerfectCompleteness.Machines.CanonicalCoarseningEncoding
import OAI.Computability.PerfectCompleteness.Machines.MetadataFreeTapeLemmas

namespace OAI


namespace PerfectCompleteness.FixedQueryCodec

open HierarchicalArrays (Nodes Block)
open MixedSupport
open scoped Classical

noncomputable section

abbrev LeftOutput (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :=
  HierarchicalArrays.Output branch n rows

def leftCount (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Nat :=
  Fintype.card (LeftOutput branch n rows)

def leftEquiv (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    LeftOutput branch n rows ≃ Fin (leftCount branch n rows) :=
  MetadataFreeSampler.outputEquiv branch n rows

def leftEncode (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    LeftOutput branch n rows → Fin (leftCount branch n rows) :=
  leftEquiv branch n rows

theorem leftEncode_injective (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Function.Injective (leftEncode branch n rows) :=
  (leftEquiv branch n rows).injective

abbrev TestIndex (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :=
  Σ node : Nodes branch n, BucketSampler.Direction (rows (Nodes.height node))

instance testIndexFintype (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Fintype (TestIndex branch n rows) := by
  unfold TestIndex
  infer_instance

variable {branch : Nat → Nat} {n t v m : Nat} {rows repeats : Nat → Nat}

abbrev RightOutput (θ : TestIndex branch n rows) : Type :=
  DirectionQuotient.Space θ.2.val ×
    (BlockQuotient.OtherBlocks (fun node : Nodes branch n => Block rows node) θ.1 × PUnit.{1})

instance rightOutputFintype (θ : TestIndex branch n rows) : Fintype (RightOutput θ) :=
  Fintype.ofFinite _

def project (θ : TestIndex branch n rows) : LeftOutput branch n rows → RightOutput θ :=
  BlockQuotient.projectBlock (I := Nodes branch n)
    (V := fun node : Nodes branch n => Block rows node) (B := PUnit.{1}) θ.1 θ.2.val

abbrev TaggedRight (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Type :=
  Σ θ : TestIndex branch n rows, RightOutput θ

instance taggedRightFintype (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Fintype (TaggedRight branch n rows) := by
  letI : (θ : TestIndex branch n rows) → Fintype (RightOutput θ) :=
    fun θ => rightOutputFintype θ
  unfold TaggedRight
  infer_instance

def rightCount (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Nat :=
  Fintype.card (TaggedRight branch n rows)

def rightEquiv (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    TaggedRight branch n rows ≃ Fin (rightCount branch n rows) :=
  Fintype.equivFin _

def rightEncode (θ : TestIndex branch n rows) :
    RightOutput θ → Fin (rightCount branch n rows) :=
  fun z => rightEquiv branch n rows ⟨θ, z⟩

theorem rightEncode_injective (θ : TestIndex branch n rows) :
    Function.Injective (rightEncode θ) :=
  (rightEquiv branch n rows).injective.comp (sigma_mk_injective (i := θ))

def outputMap (θ : TestIndex branch n rows) :
    Fin (leftCount branch n rows) → Fin (rightCount branch n rows) :=
  fun a => rightEncode θ (project θ ((leftEquiv branch n rows).symm a))

@[simp] theorem outputMap_leftEncode (θ : TestIndex branch n rows)
    (y : LeftOutput branch n rows) :
    outputMap θ (leftEncode branch n rows y) = rightEncode θ (project θ y) := by
  change rightEncode θ (project θ
    ((leftEquiv branch n rows).symm (leftEquiv branch n rows y))) = _
  rw [(leftEquiv branch n rows).symm_apply_apply]

def decodedFiberEquiv (θ : TestIndex branch n rows) (z : RightOutput θ) :
    {a : Fin (leftCount branch n rows) //
      project θ ((leftEquiv branch n rows).symm a) = z} ≃
    {y : LeftOutput branch n rows // project θ y = z} :=
  Equiv.subtypeEquivOfSubtype (p := fun y : LeftOutput branch n rows => project θ y = z)
    (leftEquiv branch n rows).symm

theorem outputMap_fiber_le_two (θ : TestIndex branch n rows)
    (b : Fin (rightCount branch n rows)) :
    Nat.card {a : Fin (leftCount branch n rows) // outputMap θ a = b} ≤ 2 := by
  have hsmall : ∀ z : RightOutput θ,
      Nat.card {a : Fin (leftCount branch n rows) //
        project θ ((leftEquiv branch n rows).symm a) = z} ≤ 2 := by
    intro z
    have hc := (Nat.card_congr (decodedFiberEquiv θ z)).trans
      (BlockQuotient.card_projectBlock_fiber (I := Nodes branch n)
        (V := fun node : Nodes branch n => Block rows node) (B := PUnit.{1})
        θ.1 θ.2.val θ.2.property z)
    exact hc.le
  by_cases hb : ∃ z : RightOutput θ, rightEncode θ z = b
  · obtain ⟨z, rfl⟩ := hb
    let e :
        {a : Fin (leftCount branch n rows) // outputMap θ a = rightEncode θ z} ≃
        {a : Fin (leftCount branch n rows) //
          project θ ((leftEquiv branch n rows).symm a) = z} :=
      Equiv.subtypeEquivRight (fun a => by
        change (rightEncode θ (project θ ((leftEquiv branch n rows).symm a)) =
          rightEncode θ z) ↔ _
        exact ⟨fun h => (rightEncode_injective θ) h,
          fun h => congrArg (rightEncode θ) h⟩)
    exact (Nat.card_congr e).le.trans (hsmall z)
  · let : IsEmpty {a : Fin (leftCount branch n rows) // outputMap θ a = b} :=
      ⟨fun a => hb
        ⟨project θ ((leftEquiv branch n rows).symm a.val), a.property⟩⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le 2

section Keys

variable {k : Nat}

theorem left_key (side : CanonicalKeys.Side) (slots : Fin k → Slot)
    (f : Assignment slots → LeftOutput branch n rows) :
    CanonicalKeys.key side slots (leftEncode branch n rows ∘ f) =
      CanonicalKeys.key side slots f :=
  CanonicalCoarseningEncoding.key_fine side slots f
    (leftEncode branch n rows) (leftEncode_injective branch n rows)

theorem right_key (side : CanonicalKeys.Side) (slots : Fin k → Slot)
    (f : Assignment slots → LeftOutput branch n rows) (θ : TestIndex branch n rows) :
    CanonicalKeys.key side slots (outputMap θ ∘ (leftEncode branch n rows ∘ f)) =
      CanonicalKeys.key side slots (project θ ∘ f) :=
  CanonicalCoarseningEncoding.key_coarse side slots f (project θ)
    (leftEncode branch n rows) (rightEncode θ) (outputMap θ)
    (rightEncode_injective θ) (outputMap_leftEncode θ)

theorem right_kernel (slots : Fin k → Slot)
    (f : Assignment slots → LeftOutput branch n rows) (θ : TestIndex branch n rows) :
    ∀ x x', (project θ ∘ f) x = (project θ ∘ f) x' ↔
      (outputMap θ ∘ (leftEncode branch n rows ∘ f)) x =
        (outputMap θ ∘ (leftEncode branch n rows ∘ f)) x' :=
  CanonicalCoarseningEncoding.coarseKernel slots f (project θ)
    (leftEncode branch n rows) (rightEncode θ) (outputMap θ)
    (rightEncode_injective θ) (outputMap_leftEncode θ)

end Keys

def leftTable {slots : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (arrays : HierarchicalArrays.Arrays slots rows) :
    Assignment (TreeCanonical.numberedSlots slots) → Fin (leftCount branch n rows) :=
  leftEncode branch n rows ∘
    TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays)

theorem leftTable_key (side : CanonicalKeys.Side)
    {slots : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (arrays : HierarchicalArrays.Arrays slots rows) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots) (leftTable arrays) =
      TreeCanonical.key side slots (HierarchicalArrays.fullJoint arrays) :=
  left_key side (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays))

theorem rightTable_key (side : CanonicalKeys.Side)
    {slots : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (arrays : HierarchicalArrays.Arrays slots rows) (θ : TestIndex branch n rows) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots) (outputMap θ ∘ leftTable arrays) =
      TreeCanonical.key side slots (project θ ∘ HierarchicalArrays.fullJoint arrays) :=
  right_key side (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedFunction slots (HierarchicalArrays.fullJoint arrays)) θ

def testIndex (data : MetadataFreeTape.Input branch n t rows repeats) :
    TestIndex branch n rows :=
  ⟨GeometricPath.nodeAtLevel data.2.1 data.2.2.2.1, data.2.2.2.2⟩

def rawTestIndex (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) : TestIndex branch n rows :=
  ⟨GeometricPath.nodeAtLevel e.1.2 e.2.2.1, e.2.2.2⟩

@[simp] theorem testIndex_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    testIndex (MetadataFreeTape.encodeRaw clauses rows repeats e) = rawTestIndex clauses e := rfl

def withProjection {a k l : Nat} (fine : CanonicalKeyShape.Input a k)
    (p : Fin k → Fin l) : CanonicalPartialTable.Input a k l :=
  ⟨fine.1, fine.2, p⟩

def partialInput (data : MetadataFreeTape.Input branch n t rows repeats) :
    CanonicalPartialTable.Input (TreeCanonical.locationCount branch n t)
      (leftCount branch n rows) (rightCount branch n rows) :=
  withProjection (MetadataFreeTape.keyInput data) (outputMap (testIndex data))

theorem partialInput_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    partialInput (MetadataFreeTape.encodeRaw clauses rows repeats e) =
      CanonicalPartialTable.input
        (TreeCanonical.numberedSlots (MetadataFreeSampler.sourceSlots clauses e.1.1))
        (leftTable (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
          (MetadataFreeSampler.sourceSlots clauses e.1.1) e.2.1))
        (outputMap (rawTestIndex clauses e)) := by
  unfold partialInput
  rw [MetadataFreeTape.keyInput_encodeRaw, testIndex_encodeRaw]
  rfl

def rightInputOfPartial {a k l : Nat} (data : CanonicalPartialTable.Input a k l) :
    CanonicalKeyShape.Input a l :=
  ⟨data.1, data.2.2 ∘ data.2.1⟩

def rightKeyInput (data : MetadataFreeTape.Input branch n t rows repeats) :
    CanonicalKeyShape.Input (TreeCanonical.locationCount branch n t)
      (rightCount branch n rows) :=
  rightInputOfPartial (partialInput data)

theorem rightKeyInput_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    rightKeyInput (MetadataFreeTape.encodeRaw clauses rows repeats e) =
      CanonicalKeyShape.input
        (TreeCanonical.numberedSlots (MetadataFreeSampler.sourceSlots clauses e.1.1))
        (outputMap (rawTestIndex clauses e) ∘
          leftTable (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
            (MetadataFreeSampler.sourceSlots clauses e.1.1) e.2.1)) := by
  rw [rightKeyInput, partialInput_encodeRaw]
  rfl

theorem partialInput_admissible {q : Nat} (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)
    (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Admissible
      (CanonicalPartialTable.lookup hq large (partialInput data)) :=
  CanonicalPartialTable.admissible_of_output_fibers hq large (partialInput data)
    (outputMap_fiber_le_two (testIndex data))

end
end PerfectCompleteness.FixedQueryCodec

end OAI

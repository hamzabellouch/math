import OAI.Computability.PerfectCompleteness.Machines.CanonicalKeyMachine
import OAI.Computability.PerfectCompleteness.Reduction.SignedCompletionSchedule

namespace OAI

section

namespace PerfectCompleteness.DescriptorKeyTemplate

open CanonicalKeys CanonicalKeyShape MixedSupport MetadataFreeSampler ClauseSupport
open scoped Classical

noncomputable section

def occurrence : Slot → Nat
  | .clause c _ _ => c
  | .bit _ => 0

def variableIDs : Slot → Fin 3 → Nat
  | .clause _ ids _ => ids
  | .bit v => fun _ => v

@[simp] theorem actualSlot_erase (slot : Slot) :
    KeyMetadataMachine.actualSlot (erase slot) (occurrence slot) (variableIDs slot) = slot := by
  cases slot <;> rfl

structure Template (width : Nat) where
  shapes : Fin width → Shape
  modes : Fin width → SupportMode
  partition : Set (Set (Fin width → ReducedValue))

instance (width : Nat) : Finite (Template width) := by
  let : Finite ReducedValue := ReducedDomains.reducedValue_finite
  apply Finite.of_injective
    (fun template : Template width => (template.shapes, template.modes, template.partition))
  intro a b h
  cases a
  cases b
  cases h
  rfl

def ofInput {width k : Nat} (data : CanonicalKeyShape.Input width k) : Template width :=
  ⟨data.1, inputModes data, inputPartition data⟩

def recover {width : Nat} (side : Side) (template : Template width)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : Key width :=
  CanonicalKeyMachine.recoveredKey template.shapes template.modes side template.partition ids vars

theorem recover_ofInput {width k : Nat} (side : Side) (slots : Fin width → Slot)
    (data : CanonicalKeyShape.Input width k) (sameShape : data.1 = shape slots) :
    recover side (ofInput data) (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) =
      CanonicalKeyShapeMachine.recoverKey side slots data := by
  have restored : CanonicalKeyMachine.actualSlots data.1
      (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) = slots := by
    funext i
    rw [sameShape]
    exact actualSlot_erase (slots i)
  change CanonicalKeyMachine.recoveredKey data.1 (inputModes data) side
    (inputPartition data) _ _ = _
  unfold CanonicalKeyMachine.recoveredKey
  rw [restored]
  rfl

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
    (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def tapeInput (descriptor : SignedCompletionSchedule.Descriptor
    (rows := rows) (repeats := repeats) hq large) :
    MetadataFreeTape.Input branch n t rows repeats := ⟨descriptor.1, descriptor.2.1⟩

def ofTape (side : Side) (data : MetadataFreeTape.Input branch n t rows repeats) :
    Template (TreeCanonical.locationCount branch n t) :=
  match side with
  | .left => ofInput (MetadataFreeTape.keyInput data)
  | .right => ofInput (FixedQueryCodec.rightKeyInput data)

def ofDescriptor (side : Side) (descriptor : SignedCompletionSchedule.Descriptor
    (rows := rows) (repeats := repeats) hq large) :
    Template (TreeCanonical.locationCount branch n t) := ofTape side (tapeInput hq large descriptor)

theorem ofDescriptor_seed_independent (side : Side) (signs : SignTuple branch n t)
    (outcome : MetadataFreeLaw.SignedOutcome signs rows repeats)
    (a b : Fin (SignedCompletionSchedule.active hq large signs outcome)) :
    ofDescriptor hq large side ⟨signs, outcome, a⟩ =
      ofDescriptor hq large side ⟨signs, outcome, b⟩ := rfl

variable {v m : Nat}

theorem recover_left (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    let slots := TreeCanonical.numberedSlots (sourceSlots clauses e.1.1)
    recover .left (ofTape .left (MetadataFreeTape.encodeRaw clauses rows repeats e))
        (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) =
      CanonicalKeys.key .left slots
        (TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
          (HierarchicalArrays.fullJoint
            (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
              (sourceSlots clauses e.1.1) e.2.1))) := by
  dsimp only
  rw [ofTape, recover_ofInput]
  · exact MetadataTapeMachine.recoverKey_encodeRaw .left clauses e
  · rw [MetadataFreeTape.keyInput_encodeRaw]
    rfl

theorem recover_right (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    let slots := TreeCanonical.numberedSlots (sourceSlots clauses e.1.1)
    recover .right (ofTape .right (MetadataFreeTape.encodeRaw clauses rows repeats e))
        (fun i => occurrence (slots i)) (fun i => variableIDs (slots i)) =
      CanonicalKeys.key .right slots
        (FixedQueryCodec.project (FixedQueryCodec.rawTestIndex clauses e) ∘
          TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
            (HierarchicalArrays.fullJoint
              (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
                (sourceSlots clauses e.1.1) e.2.1))) := by
  dsimp only
  rw [ofTape, recover_ofInput]
  · exact FiniteConstraintMachine.recover_right_key clauses e
  · rw [FixedQueryCodec.rightKeyInput_encodeRaw]
    rfl

theorem writer_payload {width : Nat} (side : Side) (template : Template width)
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) :
    CanonicalKeyMachine.payload template.shapes template.modes side template.partition ids vars =
      CanonicalKeyEncoding.bits (recover side template ids vars) ++ [true] := rfl

end
end PerfectCompleteness.DescriptorKeyTemplate

end

end OAI

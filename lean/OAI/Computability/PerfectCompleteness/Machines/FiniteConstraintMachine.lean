import OAI.Computability.PerfectCompleteness.Machines.LocalCompletionMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.MetadataFreeTapeLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedQueryCodec

namespace OAI

section

namespace PerfectCompleteness.FiniteConstraintMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MetadataFreeSampler

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
    (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

def localInput (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Input q :=
  CanonicalPartialTable.lookup hq large (FixedQueryCodec.partialInput data)

def result (data : MetadataFreeTape.Input branch n t rows repeats) : LocalCompletionFamily.Result q :=
  LocalCompletionFamily.lookup hq (localInput hq large data)

theorem result_correct (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionFamily.Correct (localInput hq large data) (result hq large data) :=
  LocalCompletionFamily.lookup_correct hq _ (FixedQueryCodec.partialInput_admissible hq large data)

def keyWords (data : MetadataFreeTape.Input branch n t rows repeats) : List Nat :=
  CanonicalKeyShapeMachine.outputWords (MetadataFreeTape.keyInput data) ++
    CanonicalKeyShapeMachine.outputWords (FixedQueryCodec.rightKeyInput data)

def keyWidth (branch : Nat → Nat) (n t : Nat) : Nat :=
  2 * (TreeCanonical.locationCount branch n t +
    CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t))

theorem keyWords_length (data : MetadataFreeTape.Input branch n t rows repeats) :
    (keyWords data).length = keyWidth branch n t := by
  simp only [keyWords, List.length_append, CanonicalKeyShapeMachine.outputWords_length, keyWidth]
  omega

def outputWords (data : MetadataFreeTape.Input branch n t rows repeats) : List Nat :=
  keyWords data ++ LocalCompletionSerialization.payloadWords (result hq large data)

def outputBits (data : MetadataFreeTape.Input branch n t rows repeats) : List Bool :=
  encodeWords (outputWords hq large data)

theorem outputWords_drop_keys (data : MetadataFreeTape.Input branch n t rows repeats) :
    (outputWords hq large data).drop (keyWidth branch n t) =
      LocalCompletionSerialization.payloadWords (result hq large data) := by
  exact List.drop_left' (keyWords_length data)

theorem parse_output_payload (data : MetadataFreeTape.Input branch n t rows repeats) :
    LocalCompletionSerialization.parsePayload q
        ((outputWords hq large data).drop (keyWidth branch n t)) =
      some ((List.finRange (LocalCompletionFamily.activeCount (result hq large data))).map
        (LocalCompletionSerialization.projection (result_correct hq large data))) := by
  rw [outputWords_drop_keys]
  exact LocalCompletionSerialization.parse_payload (result_correct hq large data)

theorem decode_outputBits (data : MetadataFreeTape.Input branch n t rows repeats) :
    decodeWords (outputBits hq large data) = some (outputWords hq large data) :=
  decodeWords_encodeWords _

theorem outputWords_length_le (data : MetadataFreeTape.Input branch n t rows repeats) :
    (outputWords hq large data).length ≤ keyWidth branch n t + 1 + (2 * q) * (2 * q) := by
  rw [outputWords, List.length_append, keyWords_length, LocalCompletionSerialization.payloadWords_length]
  have h := Nat.mul_le_mul_right (2 * q) (LocalCompletionFamily.activeCount_le (result hq large data))
  omega

def emit : MetadataTapeMachine.Symbol branch n t rows repeats → List Bool
  | none => []
  | some data => outputBits hq large data

def computation :
    TM2ComputableInPolyTime
      (MetadataTapeMachine.inputBits (branch := branch) (n := n) (t := t)
        (rows := rows) (repeats := repeats)) id (emit hq large) :=
  FiniteWordMachine.computation (MetadataTapeMachine.inputEnum branch n t rows repeats)
    none (emit hq large)

def machine_output (data : MetadataFreeTape.Input branch n t rows repeats) :
    TM2OutputsInTime (computation (rows := rows) (repeats := repeats) hq large).tm
      (MetadataTapeMachine.inputBits (some data)) (some (outputBits hq large data)) 1 := by
  have h := (computation (rows := rows) (repeats := repeats) hq large).outputsFun (some data)
  change TM2OutputsInTime (computation (rows := rows) (repeats := repeats) hq large).tm
    ((MetadataTapeMachine.inputBits (some data)).map id)
    (some ((outputBits hq large data).map id)) ((1 : Polynomial Nat).eval _) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) => TM2OutputsInTime (computation (rows := rows) (repeats := repeats) hq large).tm i (some o) 1)
    (List.map_id (MetadataTapeMachine.inputBits (some data)))
    (List.map_id (outputBits hq large data))) h

variable {v m : Nat}

theorem recover_right_key (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    CanonicalKeyShapeMachine.recoverKey .right
        (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (FixedQueryCodec.rightKeyInput (MetadataFreeTape.encodeRaw clauses rows repeats e)) =
      CanonicalKeys.key .right (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (FixedQueryCodec.project (FixedQueryCodec.rawTestIndex clauses e) ∘
          TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
            (HierarchicalArrays.fullJoint
              (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
                (sourceSlots clauses e.1.1) e.2.1))) := by
  rw [FixedQueryCodec.rightKeyInput_encodeRaw, CanonicalKeyShapeMachine.recoverKey_input]
  exact FixedQueryCodec.right_key .right _ _ (FixedQueryCodec.rawTestIndex clauses e)

theorem parsed_projection (data : MetadataFreeTape.Input branch n t rows repeats)
    (seed : Fin (LocalCompletionFamily.activeCount (result hq large data))) (a : Fin (2 * q)) :
    (LocalCompletionSerialization.projection (result_correct hq large data) seed).images[a] =
      LocalCompletionFamily.table (result hq large data) seed a :=
  LocalCompletionSerialization.projection_apply (result_correct hq large data) seed a

theorem workAlphabet_finite (tape : (computation (rows := rows) (repeats := repeats) hq large).tm.K) :
    Finite ((computation (rows := rows) (repeats := repeats) hq large).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.FiniteConstraintMachine

end

end OAI

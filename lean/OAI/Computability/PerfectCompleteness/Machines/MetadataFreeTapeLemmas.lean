import OAI.Computability.PerfectCompleteness.Machines.CanonicalKeyShapeMachineLemmas
import OAI.Computability.PerfectCompleteness.Sampling.MetadataFreeSampler

namespace OAI


namespace PerfectCompleteness.MetadataFreeTape

open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open HierarchicalArrays (Arrays Nodes)
open MetadataFreeSampler
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n d t v m : Nat}

def tapeEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d) :
    ∀ q : PreliminarySampler.Questions branch n t m,
      WholeArraySampler.Tape rows repeats p (sourceSlots clauses q) ≃
        WholeArraySampler.Tape rows repeats p (dummyTreeSlots (sourceSigns clauses q)) := by
  induction p with
  | refl n =>
      intro q
      exact Equiv.refl _
  | @step n d i p ih =>
      intro q
      refine Equiv.piCongrRight (fun k => ?_)
      rcases k with u | (u | j)
      · exact Equiv.refl _
      · exact ih (fun leaf k => q (i, leaf) k)
      · exact Equiv.refl _

@[simp] theorem tapeEquiv_root (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (ω : WholeArraySampler.Tape rows repeats (.step i p) (sourceSlots clauses q)) :
    tapeEquiv clauses rows repeats (.step i p) q ω (.inl ()) = ω (.inl ()) := rfl

@[simp] theorem tapeEquiv_selected (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (ω : WholeArraySampler.Tape rows repeats (.step i p) (sourceSlots clauses q)) :
    tapeEquiv clauses rows repeats (.step i p) q ω (.inr (.inl ())) =
      tapeEquiv clauses rows repeats p (fun leaf k => q (i, leaf) k)
        (ω (.inr (.inl ()))) := rfl

@[simp] theorem tapeEquiv_ordinary (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (i : Fin (branch n)) (p : Path branch n d)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (ω : WholeArraySampler.Tape rows repeats (.step i p) (sourceSlots clauses q))
    (j : RecursiveSampler.OffPath i) :
    tapeEquiv clauses rows repeats (.step i p) q ω (.inr (.inr j)) =
      ω (.inr (.inr j)) := rfl

theorem evaluate_tapeEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (p : Path branch n d) :
    ∀ (q : PreliminarySampler.Questions branch n t m)
      (ω : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)),
      WholeArraySampler.evaluate rows repeats p (dummyTreeSlots (sourceSigns clauses q))
          (tapeEquiv clauses rows repeats p q ω) =
        WholeArraySampler.evaluate rows repeats p (sourceSlots clauses q) ω := by
  induction p with
  | refl n =>
      intro q ω
      rfl
  | @step n d i p ih =>
      intro q ω
      funext node
      rcases node with u | ⟨j, node⟩
      · cases u
        rfl
      · by_cases hji : j = i
        · subst j
          have hinner := congrFun
            (ih (fun leaf k => q (i, leaf) k) (ω (.inr (.inl ())))) node
          exact (WholeArraySampler.evaluate_selected rows repeats i p
            (dummyTreeSlots (sourceSigns clauses q))
            (tapeEquiv clauses rows repeats (.step i p) q ω) node).trans
              (hinner.trans (WholeArraySampler.evaluate_selected rows repeats i p
                (sourceSlots clauses q) ω node).symm)
        · let off : RecursiveSampler.OffPath i := ⟨j, hji⟩
          exact (WholeArraySampler.evaluate_ordinary rows repeats i p
            (dummyTreeSlots (sourceSigns clauses q))
            (tapeEquiv clauses rows repeats (.step i p) q ω) off node).trans
              (WholeArraySampler.evaluate_ordinary rows repeats i p
                (sourceSlots clauses q) ω off node).symm

def evaluateSignedTape (signs : SignTuple branch n t) (rows repeats : Nat → Nat)
    (p : Path branch n d)
    (ω : WholeArraySampler.Tape rows repeats p (dummyTreeSlots signs)) :
    MetadataFreeSampler.Input branch n t rows :=
  (signs, fun node row x =>
    HierarchicalArrays.joint
      (WholeArraySampler.evaluate rows repeats p (dummyTreeSlots signs) ω)
      ((assignmentEquiv signs).symm x) node row)

theorem evaluateSignedTape_tapeEquiv
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (rows repeats : Nat → Nat)
    (p : Path branch n d)
    (ω : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)) :
    evaluateSignedTape (sourceSigns clauses q) rows repeats p
        (tapeEquiv clauses rows repeats p q ω) =
      MetadataFreeSampler.encodeTape clauses q rows repeats p ω := by
  apply Prod.ext
  · rfl
  · funext node row x
    exact congrArg
      (fun arrays : Arrays (sourceSlots clauses q) rows =>
        HierarchicalArrays.joint arrays ((sourceAssignmentEquiv clauses q).symm x) node row)
      (evaluate_tapeEquiv clauses rows repeats p q ω)

abbrev Input (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  Σ signs : SignTuple branch n t, Σ leaf : Slots branch n,
    WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs) ×
      PreliminarySampler.Choice rows leaf

instance inputFintype (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    Fintype (Input branch n t rows repeats) := by
  letI : (signs : SignTuple branch n t) → (leaf : Slots branch n) → Fintype
      (WholeArraySampler.Tape rows repeats (GeometricPath.leafPath leaf) (dummyTreeSlots signs) ×
        PreliminarySampler.Choice rows leaf) := fun signs leaf => inferInstance
  unfold Input
  infer_instance

def evaluate {rows repeats : Nat → Nat} (data : Input branch n t rows repeats) :
    MetadataFreeSampler.Input branch n t rows :=
  evaluateSignedTape data.1 rows repeats (GeometricPath.leafPath data.2.1) data.2.2.1

def encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) : Input branch n t rows repeats :=
  ⟨sourceSigns clauses e.1.1, e.1.2,
    tapeEquiv clauses rows repeats (GeometricPath.leafPath e.1.2) e.1.1 e.2.1, e.2.2⟩

theorem evaluate_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    evaluate (encodeRaw clauses rows repeats e) =
      MetadataFreeSampler.encodeTape clauses e.1.1 rows repeats
        (GeometricPath.leafPath e.1.2) e.2.1 :=
  evaluateSignedTape_tapeEquiv clauses e.1.1 rows repeats (GeometricPath.leafPath e.1.2) e.2.1

def keyInput {rows repeats : Nat → Nat} (data : Input branch n t rows repeats) :
    CanonicalKeyShape.Input (TreeCanonical.locationCount branch n t)
      (Fintype.card (HierarchicalArrays.Output branch n rows)) :=
  MetadataFreeSampler.shapeInput (evaluate data)

theorem keyInput_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    keyInput (encodeRaw clauses rows repeats e) =
      CanonicalKeyShape.input (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (outputEquiv branch n rows ∘ TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
          (HierarchicalArrays.fullJoint
            (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
              (sourceSlots clauses e.1.1) e.2.1))) := by
  rw [keyInput, evaluate_encodeRaw]
  exact shapeInput_encodeInput clauses e.1.1 _

end
end PerfectCompleteness.MetadataFreeTape


namespace PerfectCompleteness.MetadataTapeMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MetadataFreeTape MetadataFreeSampler

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {rows repeats : Nat → Nat}

abbrev Symbol (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  Option (MetadataFreeTape.Input branch n t rows repeats)

def inputEnum (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    Symbol branch n t rows repeats ≃ Fin (Fintype.card (Symbol branch n t rows repeats)) :=
  Fintype.equivFin _

def inputBits (data : Symbol branch n t rows repeats) : List Bool :=
  FiniteBlockMachine.word (inputEnum branch n t rows repeats) data

def outputBits : Symbol branch n t rows repeats → List Bool
  | none => []
  | some data => CanonicalKeyShapeMachine.outputBits (MetadataFreeTape.keyInput data)

def computation (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    TM2ComputableInPolyTime
      (inputBits (branch := branch) (n := n) (t := t) (rows := rows) (repeats := repeats))
      id outputBits :=
  FiniteWordMachine.computation (inputEnum branch n t rows repeats) none outputBits

def machine_output (data : Symbol branch n t rows repeats) :
    TM2OutputsInTime (computation branch n t rows repeats).tm
      (inputBits data) (some (outputBits data)) 1 := by
  have h := (computation branch n t rows repeats).outputsFun data
  change TM2OutputsInTime (computation branch n t rows repeats).tm
    ((inputBits data).map id) (some ((outputBits data).map id))
    ((1 : Polynomial Nat).eval _) at h
  rw [Polynomial.eval_one] at h
  exact Eq.mp (congrArg₂
    (fun (i o : List Bool) =>
      TM2OutputsInTime (computation branch n t rows repeats).tm i (some o) 1)
    (List.map_id (inputBits data)) (List.map_id (outputBits data))) h

theorem statement_trace {K Λ : Type} [DecidableEq K]
    (src dst : K) (exit : Option Λ) (hne : src ≠ dst)
    (data : Symbol branch n t rows repeats) (suffix : List Bool)
    (state : FiniteWordMachine.State (Fintype.card (Symbol branch n t rows repeats)))
    (tapes : K → List Bool) (hinput : tapes src = inputBits data ++ suffix) :
    TM2.stepAux (FiniteWordMachine.statement src dst exit
        (inputEnum branch n t rows repeats) none outputBits) state tapes = {
      l := exit
      var := ((), UniqueGamesTheorem.Foundations.Complexity.MachineFixedBlockMap.emptyBuffer _)
      stk := Function.update (Function.update tapes src suffix) dst
        (outputBits data ++ tapes dst)
    } :=
  FiniteWordMachine.statement_trace src dst exit hne
    (inputEnum branch n t rows repeats) none data outputBits suffix state tapes hinput

variable {v m : Nat}

theorem outputBits_encodeRaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    outputBits (some (MetadataFreeTape.encodeRaw clauses rows repeats e)) =
      CanonicalKeyShapeMachine.outputBits
        (CanonicalKeyShape.input
          (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
          (outputEquiv branch n rows ∘ TreeCanonical.numberedFunction
            (sourceSlots clauses e.1.1) (HierarchicalArrays.fullJoint
              (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
                (sourceSlots clauses e.1.1) e.2.1)))) := by
  change CanonicalKeyShapeMachine.outputBits
    (MetadataFreeTape.keyInput (MetadataFreeTape.encodeRaw clauses rows repeats e)) = _
  rw [MetadataFreeTape.keyInput_encodeRaw]

theorem recoverKey_encodeRaw (side : CanonicalKeys.Side)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    CanonicalKeyShapeMachine.recoverKey side
        (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (MetadataFreeTape.keyInput (MetadataFreeTape.encodeRaw clauses rows repeats e)) =
      CanonicalKeys.key side (TreeCanonical.numberedSlots (sourceSlots clauses e.1.1))
        (TreeCanonical.numberedFunction (sourceSlots clauses e.1.1)
          (HierarchicalArrays.fullJoint
            (WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
              (sourceSlots clauses e.1.1) e.2.1))) := by
  rw [MetadataFreeTape.keyInput_encodeRaw, CanonicalKeyShapeMachine.recoverKey_input]
  exact CanonicalKeys.key_postcomp_equiv side _ _ (outputEquiv branch n rows)

theorem actual_machine_output (clauses : Fin m → SourceClause.NormalizedClause v)
    (e : PreliminarySampler.Raw clauses branch n t rows repeats) :
    Nonempty (TM2OutputsInTime (computation branch n t rows repeats).tm
      (inputBits (some (MetadataFreeTape.encodeRaw clauses rows repeats e)))
      (some (CanonicalKeyShapeMachine.outputBits
        (MetadataFreeTape.keyInput (MetadataFreeTape.encodeRaw clauses rows repeats e)))) 1) :=
  ⟨machine_output (some (MetadataFreeTape.encodeRaw clauses rows repeats e))⟩

theorem workAlphabet_finite (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (tape : (computation branch n t rows repeats).tm.K) :
    Finite ((computation branch n t rows repeats).tm.Γ tape) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.MetadataTapeMachine

end OAI

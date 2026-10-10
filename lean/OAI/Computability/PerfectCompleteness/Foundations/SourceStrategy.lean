import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Machines.DomainEncoding

namespace OAI

section

namespace PerfectCompleteness.ReducedPartition

variable {X W R Y Z : Type*}

theorem fiber_eq_of_parts_eq_of_reduction_eq
    (rX : X → R) (rW : W → R) (f : X → Y) (g : W → Z)
    (hg : ConstantOnFibers rW g) (hparts : parts rX f = parts rW g)
    (x : X) (w : W) (hpoint : rX x = rW w) :
    fiber rX f x = fiber rW g w := by
  have hmem : fiber rX f x ∈ parts rW g := by
    rw [← hparts]
    exact ⟨x, rfl⟩
  obtain ⟨w', hw'⟩ := hmem
  have hw : rW w ∈ fiber rW g w' := by
    rw [hw', ← hpoint]
    exact self_mem_fiber rX f x
  have hvalue : g w = g w' := (mem_fiber_iff rW g hg w w').mp hw
  exact hw'.symm.trans (fiber_eq_of_output_eq rW g hvalue).symm

end PerfectCompleteness.ReducedPartition

namespace PerfectCompleteness.SourceKeys

open SourceClause ClauseSupport MixedSupport CanonicalKeys

variable {v m n : Nat} {C Y Z : Type*}

def assignmentAt (assignment : Fin v → Bool) (j : Nat) : Bool :=
  if h : j < v then assignment ⟨j, h⟩ else false

@[simp] theorem assignmentAt_fin (assignment : Fin v → Bool) (j : Fin v) :
    assignmentAt assignment j.val = assignment j := by
  simp [assignmentAt, j.isLt]

def valueOfKey (clauses : Fin m → NormalizedClause v) (assignment : Fin v → Bool) :
    SlotKey → ReducedValue
  | .dropped => .dropped
  | .bit j => .bit (assignmentAt assignment j)
  | .full c _ =>
      .full (if h : c < m then (clauses ⟨c, h⟩).restrict assignment else (false, false, false))

theorem localReduction_endpointValue (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (s : Endpoint v m) (f : C → (slot clauses s).Domain → Y) :
    localReduction (slot clauses s) f (endpointValue clauses assignment hsat s) =
      valueOfKey clauses assignment (localKey (slot clauses s) f) := by
  classical
  cases s with
  | clause c =>
    change C → Answer (clauses c).signs → Y at f
    change clauseReduction f (endpointValue clauses assignment hsat (.clause c)) =
      valueOfKey clauses assignment
        (clauseKey c.val (fun i => ((clauses c).variable i).val) f)
    cases hm : clauseMode f with
    | dropped => simp [clauseReduction, clauseKey, hm, reduceByMode, valueOfKey]
    | bit i =>
      simp only [clauseReduction, clauseKey, hm, reduceByMode, valueOfKey, assignmentAt_fin]
      change ReducedValue.bit (((clauses c).restrict assignment).at i) =
        ReducedValue.bit (assignment ((clauses c).variable i))
      exact congrArg ReducedValue.bit (coordinate_restrict (clauses c) assignment i)
    | full =>
      simp [clauseReduction, clauseKey, hm, reduceByMode, valueOfKey, c.isLt, endpointValue]
  | «variable» j =>
    change C → Bool → Y at f
    change bitReduction f (assignment j) = valueOfKey clauses assignment (bitKey j.val f)
    by_cases hu : Unused f
    · simp [bitReduction, bitKey, hu, valueOfKey]
    · simp [bitReduction, bitKey, hu, valueOfKey]

theorem reduction_realizingAssignment (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : Fin n → Endpoint v m)
    (f : Assignment (slot clauses ∘ endpoints) → Y) :
    reduction (slot clauses ∘ endpoints) f (realizingAssignment clauses assignment hsat endpoints) =
      fun i => valueOfKey clauses assignment (keyFields (slot clauses ∘ endpoints) f i) := by
  funext i
  exact localReduction_endpointValue clauses assignment hsat (endpoints i)
    (sectionFunction (slot clauses ∘ endpoints) f i)

theorem evaluated_label_eq_of_key_eq (clauses : Fin m → NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (side side' : Side) (source target : Fin n → Endpoint v m)
    (f : Assignment (slot clauses ∘ source) → Y)
    (g : Assignment (slot clauses ∘ target) → Z)
    (hkey : key side (slot clauses ∘ source) f = key side' (slot clauses ∘ target) g) :
    (evaluateLabel (slot clauses ∘ source) f
      (realizingAssignment clauses assignment hsat source)).val =
    (evaluateLabel (slot clauses ∘ target) g
      (realizingAssignment clauses assignment hsat target)).val := by
  have hfields : keyFields (slot clauses ∘ source) f = keyFields (slot clauses ∘ target) g :=
    DomainEncoding.keyFields_eq_of_retainedKeys_eq _ _ f g
      (congrArg (fun k : Key n => k.retained) hkey)
  have hparts : partition (slot clauses ∘ source) f = partition (slot clauses ∘ target) g :=
    congrArg (fun k : Key n => k.partition) hkey
  have hpoint :
      reduction (slot clauses ∘ source) f (realizingAssignment clauses assignment hsat source) =
      reduction (slot clauses ∘ target) g (realizingAssignment clauses assignment hsat target) := by
    rw [reduction_realizingAssignment, reduction_realizingAssignment, hfields]
  exact ReducedPartition.fiber_eq_of_parts_eq_of_reduction_eq
    (reduction (slot clauses ∘ source) f) (reduction (slot clauses ∘ target) g) f g
    (constantOnFibers (slot clauses ∘ target) g) hparts _ _ hpoint

end PerfectCompleteness.SourceKeys

end

end OAI

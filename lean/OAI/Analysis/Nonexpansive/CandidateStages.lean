import OAI.Analysis.Nonexpansive.CandidateLevel
import OAI.Analysis.Nonexpansive.FrontierTower
import OAI.Analysis.Nonexpansive.TerminalSequence

namespace OAI

/-!
# The actual recursively constructed infinite frontier tower

A stage is an already constructed finite frontier with its chronological
candidate counter and the actual ancestor maps. The next stage is obtained
by the concrete finite parent selections. No infinite tree, future detector,
or future coefficient is supplied to this recursion.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace CandidateContext

variable {D : NormalizedMinimalData (X := X)} (C : CandidateContext D)

/-- A conservative positive tolerance using the complete candidate counter.
Its comparison with the retained-budget tolerance is proved
separately after the global labels are extracted. -/
def runTolerance : ℝ := (1 / 2 : ℝ) ^ C.depth * candidateBudget C.base

theorem runTolerance_pos : 0 < C.runTolerance :=
  mul_pos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _) (candidateBudget_pos _)

variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (hanchor : C.anchor = A.x)

/-- The actual extension used at this stage. -/
def selectedExtension : FrontierExtension C.frontier :=
  C.levelExtension A hanchor C.runTolerance_pos

/-- Candidate counts include every map chosen before zero coefficients are removed. -/
def candidateCount : ℕ :=
  OrderedGroupConcat.total (fun p => (C.group A hanchor C.runTolerance_pos p).N)

theorem candidateCount_pos : 0 < C.candidateCount A hanchor := by
  apply OrderedGroupConcat.total_pos _ C.frontier.size_pos
  intro p
  exact (C.group A hanchor C.runTolerance_pos p).N_pos

/-- Advance to the next finite frontier using only the completed choices. -/
def advance : CandidateContext D where
  frontier := (C.selectedExtension A hanchor).toFrontier
  frontier_generated := C.levelExtension_generated A hanchor C.runTolerance_pos
  anchor := C.anchor
  terminal := C.terminal
  ultrafilter := C.ultrafilter
  depth := C.depth + 1
  base := C.base + C.candidateCount A hanchor
  ancestors := fun c =>
    C.ancestors ((C.selectedExtension A hanchor).parent c) ++
      [⟨C.frontier.map ((C.selectedExtension A hanchor).parent c),
        C.frontier_generated ((C.selectedExtension A hanchor).parent c)⟩]

@[simp] theorem advance_frontier :
    (C.advance A hanchor).frontier = (C.selectedExtension A hanchor).toFrontier := rfl

@[simp] theorem advance_anchor : (C.advance A hanchor).anchor = C.anchor := rfl

@[simp] theorem advance_terminal : (C.advance A hanchor).terminal = C.terminal := rfl

@[simp] theorem advance_ultrafilter : (C.advance A hanchor).ultrafilter = C.ultrafilter := rfl

@[simp] theorem advance_depth : (C.advance A hanchor).depth = C.depth + 1 := rfl

@[simp] theorem advance_base :
    (C.advance A hanchor).base = C.base + C.candidateCount A hanchor := rfl

@[simp] theorem advance_ancestors (c : Fin (C.advance A hanchor).frontier.size) :
    (C.advance A hanchor).ancestors c =
      C.ancestors ((C.selectedExtension A hanchor).parent c) ++
        [⟨C.frontier.map ((C.selectedExtension A hanchor).parent c),
          C.frontier_generated ((C.selectedExtension A hanchor).parent c)⟩] := rfl

end CandidateContext

/-- An actual stage remembers that its anchor is the one selected initially. -/
abbrev AnchoredCandidateContext (D : NormalizedMinimalData (X := X))
    (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive)) :=
  {C : CandidateContext D // C.anchor = A.x}

namespace AnchoredCandidateContext

variable (D : NormalizedMinimalData (X := X))
variable (A : AnchorPoint (tailFamily D.closed D.convex D.T D.nonexpansive))
variable (U : Ultrafilter ℕ)

/-- The initial frontier consists solely of the identity map at the root. -/
def initial : AnchoredCandidateContext D A :=
  ⟨{
    frontier := TreeFrontier.root D.convex
    frontier_generated := fun _ => Generated.id
    anchor := A.x
    terminal := terminalSequence D.closed D.convex D.T D.nonexpansive A.x
    ultrafilter := U
    depth := 1
    base := 0
    ancestors := fun _ => []
  }, rfl⟩

/-- One concrete finite stage, with the original anchor preserved. -/
def next (S : AnchoredCandidateContext D A) : AnchoredCandidateContext D A :=
  ⟨S.val.advance A S.property, S.property⟩

/-- Ordinary natural recursion constructs all finite levels successively. -/
def stages : ℕ → AnchoredCandidateContext D A
  | 0 => initial D A U
  | k + 1 => next D A (stages k)

@[simp] theorem stages_zero : stages D A U 0 = initial D A U := rfl

@[simp] theorem stages_succ (k : ℕ) :
    stages D A U (k + 1) = next D A (stages D A U k) := rfl

def context (k : ℕ) : CandidateContext D := (stages D A U k).val

theorem context_anchor (k : ℕ) : (context D A U k).anchor = A.x :=
  (stages D A U k).property

@[simp] theorem context_succ (k : ℕ) :
    context D A U (k + 1) =
      (context D A U k).advance A (context_anchor D A U k) := rfl

@[simp] theorem context_depth (k : ℕ) : (context D A U k).depth = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (context D A U k).depth + 1 = (k + 1) + 1
      rw [ih]

@[simp] theorem context_terminal (k : ℕ) :
    (context D A U k).terminal =
      terminalSequence D.closed D.convex D.T D.nonexpansive A.x := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

@[simp] theorem context_ultrafilter (k : ℕ) : (context D A U k).ultrafilter = U := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

@[simp] theorem context_base_zero : (context D A U 0).base = 0 := rfl

@[simp] theorem context_base_succ (k : ℕ) :
    (context D A U (k + 1)).base = (context D A U k).base +
      (context D A U k).candidateCount A (context_anchor D A U k) := rfl

/-- The infinite evaluated tree is extracted only after the finite recursion. -/
def tower : FrontierTower D.K where
  convex := D.convex
  frontier := fun k => (context D A U k).frontier
  step := fun k =>
    (context D A U k).selectedExtension A (context_anchor D A U k)
  zero := rfl
  next := fun _ => rfl

@[simp] theorem tower_frontier (k : ℕ) :
    (tower D A U).frontier k = (context D A U k).frontier := rfl

@[simp] theorem tower_step (k : ℕ) :
    (tower D A U).step k =
      (context D A U k).selectedExtension A (context_anchor D A U k) := rfl

/-- All maps of the resulting tree retain their concrete generated origin. -/
theorem tower_generated (k : ℕ) (v : (tower D A U).toOrderedTree.Node k) :
    Generated D.closed D.convex D.T D.nonexpansive
      ((tower D A U).toEvaluation.map k v) :=
  (context D A U k).frontier_generated v

/-- The parent return was proved for the actual new child outputs. -/
theorem tower_childAverage_near (k : ℕ)
    (p : (tower D A U).toOrderedTree.Node k) :
    ‖((tower D A U).toEvaluation.childAverage k
      (fun v => (tower D A U).toEvaluation.map (k + 1) v A.x) p : X) - (A.x : X)‖ <
        (context D A U k).runTolerance := by
  rw [(tower D A U).childAverage_agreement]
  have hmaps : (fun c => (tower D A U).toEvaluation.map (k + 1)
      (((tower D A U).nextNode k).symm c) A.x) =
      (fun c => ((tower D A U).step k).map c A.x) := by
    funext c
    have hmap := (tower D A U).toEvaluation_map_succ k
      (((tower D A U).nextNode k).symm c)
    exact congrFun (hmap.trans (congrArg ((tower D A U).step k).map
      (Equiv.apply_symm_apply ((tower D A U).nextNode k) c))) A.x
  rw [hmaps]
  have h := (context D A U k).levelExtension_childAverage_near A
    (context_anchor D A U k) (context D A U k).runTolerance_pos p
  change ‖(((tower D A U).step k).childAverage
      (fun c => ((tower D A U).step k).map c (context D A U k).anchor) p : X) -
      ((context D A U k).anchor : X)‖ < (context D A U k).runTolerance at h
  simpa only [context_anchor] using h

end AnchoredCandidateContext
end ReflexiveFixedPoints

end

end OAI

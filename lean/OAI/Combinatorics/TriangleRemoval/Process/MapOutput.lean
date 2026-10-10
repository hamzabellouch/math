import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.FreshLog

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O P Q : Type*}

def mapOutput (f : O → P) : ExposureTree K V O → ExposureTree K V P
  | .done o => .done (f o)
  | .ask k g => .ask k (fun v => mapOutput f (g v))

@[simp] theorem mapOutput_done (f : O → P) (o : O) :
    mapOutput (K := K) (V := V) f (.done o) = .done (f o) := rfl

@[simp] theorem mapOutput_bind (f : P → Q) (A : ExposureTree K V O)
    (g : O → ExposureTree K V P) :
    mapOutput f (bind A g) = bind A (fun o => mapOutput f (g o)) := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [bind, mapOutput, ih]

@[simp] theorem bind_mapOutput (f : O → P) (A : ExposureTree K V O)
    (g : P → ExposureTree K V Q) :
    bind (mapOutput f A) g = bind A (fun o => g (f o)) := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [bind, mapOutput, ih]

@[simp] theorem mapOutput_comp (f : P → Q) (g : O → P) (A : ExposureTree K V O) :
    mapOutput f (mapOutput g A) = mapOutput (f ∘ g) A := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [mapOutput, ih]

@[simp] theorem mapOutput_id (A : ExposureTree K V O) : mapOutput id A = A := by
  induction A with
  | done o => rfl
  | ask k h ih => simp only [mapOutput, ih]

@[simp] theorem fresh_mapOutput (ν : K → PMF V) (f : O → P) (A : ExposureTree K V O) :
    fresh ν (mapOutput f A) = (fresh ν A).map f := by
  induction A with
  | done o => simp [mapOutput, fresh, PMF.pure_map]
  | ask k h ih => simp only [mapOutput, fresh, ih, PMF.map_bind]

@[simp] theorem freshLog_mapOutput (ν : K → PMF V) (f : O → P) (A : ExposureTree K V O) :
    freshLog ν (mapOutput f A) = (freshLog ν A).map (fun z => (f z.1, z.2)) := by
  induction A with
  | done o => simp [mapOutput, freshLog, PMF.pure_map]
  | ask k h ih =>
    simp only [mapOutput, freshLog, ih, PMF.map_bind, PMF.map_comp]
    rfl

def checkNoneTrace {R : Type*} :
    List (ExposureTree K V (Bool × List R)) → ExposureTree K V (Bool × List R)
  | [] => .done (true, [])
  | A :: As => bind A (fun z =>
      if z.1 then .done (false, z.2)
      else mapOutput (fun y => (y.1, z.2 ++ y.2)) (checkNoneTrace As))

@[simp] theorem checkNoneTrace_outcome {R : Type*}
    (as : List (ExposureTree K V (Bool × List R))) :
    mapOutput Prod.fst (checkNoneTrace as) =
      checkNone (as.map (mapOutput Prod.fst)) := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    simp only [checkNoneTrace, mapOutput_bind, List.map_cons, checkNone,
      bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, mapOutput_done,
      mapOutput_comp]
    exact ih

end ExposureTree

section TraceQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

structure QueryCall (ι τ : Type*) where
  address : List (ι × τ)
  focus : Finset ι
  parent : Option τ

noncomputable def QueryCall.keys (H : τ → Finset ι) (c : QueryCall ι τ) : List τ :=
  (gridCandidates H c.focus c.parent).toList.map Prod.snd

noncomputable def tracedGridQuery (H : τ → Finset ι) (N : ℕ) :
    ℕ → ℕ → QueryCall ι τ → ExposureTree τ (Fin N) (Bool × List (QueryCall ι τ))
  | 0, _, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun _ => .done (true, [c]))
  | d+1, k, c => ExposureTree.bind
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H c.focus c.parent).toList)
      (fun values => ExposureTree.mapOutput (fun y => (y.1, c :: y.2))
        (ExposureTree.checkNoneTrace
          ((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
            (fun p => if p.2.val < k then
              tracedGridQuery H N d p.2.val
                ⟨p.1 :: c.address, (H p.1.2).erase p.1.1, some p.1.2⟩
              else .done (false, [])))))

theorem tracedGridQuery_outcome (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ) :
    ExposureTree.mapOutput Prod.fst (tracedGridQuery H N d k c) =
      gridQueryDepth H N d k c.focus c.parent := by
  induction d generalizing k c with
  | zero => simp only [tracedGridQuery, ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_done, gridQueryDepth]
  | succ d ih =>
    simp only [tracedGridQuery, ExposureTree.mapOutput_bind, ExposureTree.mapOutput_comp,
      gridQueryDepth]
    congr 1
    funext vals
    change ExposureTree.mapOutput Prod.fst (ExposureTree.checkNoneTrace _) = _
    rw [ExposureTree.checkNoneTrace_outcome, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    split_ifs
    · exact ih _ _
    · rfl

end TraceQuery
end SharpTerminalLeave

end

end OAI

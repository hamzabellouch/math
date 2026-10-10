import Mathlib
import OAI.Combinatorics.ThinTrees.Arithmetic.UnaryRoot
import OAI.Combinatorics.ThinTrees.Continuation.Loop
import OAI.Combinatorics.ThinTrees.Pencil.PointPrograms
import OAI.Combinatorics.ThinTrees.Pencil.SearchRealization

namespace OAI

/-! Continuation realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

abbrev graphBaseline : Realizes graphCode ratCode (fun G => baselineQ G.m) :=
  (constant graphCode ratCode 1).div ((numEdges.then natToRat).add (constant graphCode ratCode 1))
private instance poly_graphBaseline : PolyTime graphBaseline := by
  unfold graphBaseline
  apply poly_div

abbrev graphStep : Realizes graphCode ratCode (fun G => stepQ G.m) :=
  graphBaseline.div (constant graphCode ratCode 32)
private instance poly_graphStep : PolyTime graphStep := by
  unfold graphStep
  apply poly_div

def graphError : Realizes graphCode ratCode (fun G => errorQ G.n G.m) :=
  ((constant graphCode ratCode 1).div (graphSizeProgram.pow 10)).congr (by
    intro G; simp only [errorQ,_root_.zpow_neg,one_div];rfl)
instance poly_graphError : PolyTime graphError := by unfold graphError;infer_instance

def gainProgram : Realizes natCode ratCode gain :=
  (constant natCode ratCode 1).div ((unaryRoot 8 (by decide)).then natToRat)
instance poly_gainProgram : PolyTime gainProgram := by unfold gainProgram; apply poly_div

def clockProgram : Realizes (prodCode natCode natCode) natCode
    (fun p => scheduleLength p.1 p.2) :=
  ((constant (prodCode natCode natCode) natCode 32).nmul
    ((first natCode natCode).then natSucc)).nmul
      ((second natCode natCode).then (unaryRoot 16 (by decide)))
instance poly_clockProgram : PolyTime clockProgram := by
  unfold clockProgram Realizes.nmul
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_then
  · infer_instance

structure Loop where
  graph : Graph
  count : ℕ
  state : State graph.n graph.m

abbrev loopTailCode := prodCode ratCode (prodCode ratCode (prodCode matrixCode vectorCode))
abbrev loopDataCode := prodCode graphCode (prodCode natCode loopTailCode)
def Loop.data (a : Loop) :=
  (a.graph,(a.count,(a.state.scale,(a.state.quality,(matrixData a.state.matrix,List.ofFn a.state.capacity)))))
def loopCode (a : Loop) : Word := loopDataCode a.data
abbrev loopView : Realizes loopCode loopDataCode Loop.data :=
  (identity loopDataCode).reindex loopCode Loop.data (fun _ => rfl)
private instance poly_loopView : PolyTime loopView := by
  unfold loopView
  apply poly_reindex

abbrev loopGraph : Realizes loopCode graphCode Loop.graph :=
  loopView.then (first graphCode (prodCode natCode loopTailCode))
private instance poly_loopGraph : PolyTime loopGraph := by
  unfold loopGraph
  apply poly_then

abbrev loopRest := loopView.then (second graphCode (prodCode natCode loopTailCode))
abbrev loopCount : Realizes loopCode natCode Loop.count := loopRest.then (first natCode loopTailCode)
private instance poly_loopCount : PolyTime loopCount := by
  unfold loopCount
  apply poly_then

abbrev loopState := loopRest.then (second natCode loopTailCode)
abbrev loopScale : Realizes loopCode ratCode (fun a => a.state.scale) :=
  loopState.then (first ratCode (prodCode ratCode (prodCode matrixCode vectorCode)))
private instance poly_loopScale : PolyTime loopScale := by
  unfold loopScale
  apply poly_then

abbrev loopTail := loopState.then (second ratCode (prodCode ratCode (prodCode matrixCode vectorCode)))
abbrev loopQuality : Realizes loopCode ratCode (fun a => a.state.quality) :=
  loopTail.then (first ratCode (prodCode matrixCode vectorCode))
private instance poly_loopQuality : PolyTime loopQuality := by
  unfold loopQuality
  apply poly_then

abbrev loopArrays := loopTail.then (second ratCode (prodCode matrixCode vectorCode))
abbrev loopMatrix := loopArrays.then (first matrixCode vectorCode)
abbrev loopCapacity := loopArrays.then (second matrixCode vectorCode)
abbrev loopN := loopGraph.then numVertices
abbrev loopM := loopGraph.then numEdges
abbrev loopStep := loopGraph.then graphStep
abbrev loopBase := loopGraph.then graphBaseline
abbrev loopGain := loopCount.then gainProgram
abbrev loopTarget : Realizes loopCode ratCode (fun a => target a.graph.m a.count a.state.quality (gain a.count)) :=
  (loopQuality.sub ((loopGain.mul (loopCount.then natToRat)).mul loopStep)).sub
    ((constant loopCode ratCode 2).mul loopStep)

private instance poly_loopTarget : PolyTime loopTarget := by
  unfold loopTarget
  apply poly_sub

def Loop.params (a : Loop) : Params :=
  ⟨a.graph,a.state.scale,baselineQ a.graph.m,stepQ a.graph.m,
    target a.graph.m a.count a.state.quality (gain a.count),errorQ a.graph.n a.graph.m,a.state.capacity⟩
def loopParams : Realizes loopCode paramsCode Loop.params :=
  (loopGraph.both
    ((loopScale.cons (loopBase.cons (loopStep.cons (loopTarget.cons
      ((loopGraph.then graphError).then (singleton ratCode)))))).both loopCapacity)).changeOutput
        paramsCode Loop.params (fun _ => rfl)
instance poly_loopParams : PolyTime loopParams := by unfold loopParams; apply poly_changeOutput

def Loop.vector (a : Loop) := search a.graph.G a.state.scale
  (target a.graph.m a.count a.state.quality (gain a.count)) a.state.capacity

def found : Realizes loopCode pointCode (fun a => ⟨a.params,a.vector⟩) :=
  ((loopParams.both (loopParams.then solvePencil)).then pointParser).congr
    (fun a => parsePoint_ofFn a.params a.vector)
instance poly_found : PolyTime found := by unfold found; apply poly_congr

def updatedMatrix : Realizes loopCode matrixCode
    (fun a => matrixData ((update a.graph.G a.count (gain a.count) a.state).matrix)) :=
  (((((constant loopCode ratCode 1).sub loopStep).both loopMatrix).then matrixScale).both
    ((loopStep.both (found.then responsePoint)).then matrixScale)).then matrixAdd |>.congr (by
      intro a
      change matrixAddData ((matrixData a.state.matrix).map (fun row => row.map (fun x => (1-stepQ a.graph.m)*x)),
        (matrixData (qresponse (rawMatrix a.vector))).map (fun row => row.map (fun x => stepQ a.graph.m*x))) = _
      rw [matrixScale_data,matrixScale_data]
      exact matrixAdd_data _ _)
instance poly_updatedMatrix : PolyTime updatedMatrix := by unfold updatedMatrix; apply poly_congr

abbrev LoopEdge := Σ a : Loop, Fin a.graph.m
abbrev loopEdgeCode := finFamilyCode loopCode (fun a : Loop => a.graph.m)
abbrev edgeLoop : Realizes loopEdgeCode loopCode (fun x : LoopEdge => x.1) := familyFirst
abbrev edgeNumber : Realizes loopEdgeCode natCode (fun x : LoopEdge => x.2.val) := familyIndex

def updatedCapacity : Realizes loopEdgeCode ratCode
    (fun x => (update x.1.graph.G x.1.count (gain x.1.count) x.1.state).capacity x.2) :=
  let z := constant loopEdgeCode ratCode 0
  let f := edgeLoop.then found
  ((z.lt (storedU f (fun x => x.2) edgeNumber)).ite
    (z.max ((edgeCoord 1 f (fun x => x.2) edgeNumber).sub (edgeLoop.then loopBase))) z).congr
      (by intro x; simp only [update,decide_eq_true_eq];rfl)
instance poly_updatedCapacity : PolyTime updatedCapacity := by
  have hf : PolyTime (edgeLoop.then found) := by apply poly_then
  have he : PolyTime edgeNumber := by infer_instance
  unfold updatedCapacity
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_ite _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · refine @poly_lt _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · exact @poly_storedU _ _ _ _ _ _ hf he
  · refine @poly_max _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_sub _ _ _ _ _ _ ?_ ?_
      · exact @poly_edgeCoord _ _ _ _ _ _ _ hf he
      · infer_instance
  · infer_instance

def Loop.updated (a : Loop) : Loop :=
  ⟨a.graph,a.count,update a.graph.G a.count (gain a.count) a.state⟩
def updateProgram : Realizes loopCode loopCode Loop.updated :=
  (loopGraph.both (loopCount.both
    ((((constant loopCode ratCode 1).add loopStep).mul loopScale).both
      ((loopQuality.sub ((((constant loopCode ratCode 2).mul loopGain).mul
        (loopCount.then natToRat)).mul loopStep)).both
          (updatedMatrix.both (updatedCapacity.tabulateFin loopM)))))).changeOutput
            loopCode Loop.updated (fun _ => rfl)
instance poly_updateProgram : PolyTime updateProgram := by unfold updateProgram; apply poly_changeOutput

def Loop.next (a : Loop) : Loop := ⟨a.graph,a.count,advance a.graph.G a.count a.state⟩
def next : Realizes loopCode loopCode Loop.next :=
  (((loopScale.pow 4).lt (loopCount.then natToRat)).ite updateProgram (identity loopCode)).congr
    (by intro a; simp only [Loop.next,advance,decide_eq_true_eq];split <;> rfl)
instance poly_next : PolyTime next := by unfold next; apply poly_congr

lemma next_iterate (a : Loop) (i : ℕ) :
    Loop.next^[i] a=⟨a.graph,a.count,(advance a.graph.G a.count)^[i] a.state⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih]
    change Loop.mk a.graph a.count (advance _ _ _) = Loop.mk a.graph a.count _
    rw [Function.iterate_succ_apply']

abbrev extractionInputCode := prodCode graphCode natCode
abbrev extractionGraph := first graphCode natCode
abbrev extractionCount := second graphCode natCode

def initializeLoop : Realizes extractionInputCode loopCode (fun p => ⟨p.1,p.2,initial p.1.G p.2⟩) :=
  (extractionGraph.both (extractionCount.both
    ((constant extractionInputCode ratCode (1/2)).both
      ((extractionCount.then natToRat).both
        ((extractionGraph.then laplacian).both
          (((constant extractionInputCode ratCode 1).both (extractionGraph.then numEdges)).then
            (replicateList ratCode))))))).changeOutput loopCode (fun p => ⟨p.1,p.2,initial p.1.G p.2⟩)
              (by intro p; simp only [loopCode,Loop.data,initial,List.ofFn_const])
instance poly_initializeLoop : PolyTime initializeLoop := by unfold initializeLoop;infer_instance

def extract : Realizes extractionInputCode loopCode
    (fun p => ⟨p.1,p.2,extractState p.1.G p.2⟩) :=
  ((((extractionGraph.then numEdges).both extractionCount).then clockProgram).both initializeLoop).then
    next.iterate |>.congr (fun _ => next_iterate _ _)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI

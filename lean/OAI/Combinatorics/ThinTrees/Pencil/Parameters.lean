import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.GraphRealization

namespace OAI

/-! Pencil parameters. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

structure Params where
  graph : Graph
  s : ℚ
  κ : ℚ
  t : ℚ
  q : ℚ
  ε : ℚ
  u : Fin graph.m → ℚ

def Params.pencil (p : Params) := continuationPencil p.graph.G p.s p.κ p.t p.q p.ε p.u
abbrev paramsDataCode := prodCode graphCode (prodCode vectorCode vectorCode)
def Params.data (p : Params) := (p.graph,([p.s,p.κ,p.t,p.q,p.ε],List.ofFn p.u))
def paramsCode (p : Params) : Word := paramsDataCode p.data
abbrev paramsView : Realizes paramsCode paramsDataCode Params.data :=
  (identity paramsDataCode).reindex paramsCode Params.data (fun _ => rfl)
private instance poly_paramsView : PolyTime paramsView := by
  unfold paramsView
  apply poly_reindex

abbrev paramsGraph : Realizes paramsCode graphCode Params.graph := paramsView.then (first graphCode (prodCode vectorCode vectorCode))
private instance poly_paramsGraph : PolyTime paramsGraph := by
  unfold paramsGraph
  apply poly_then

abbrev paramsTail := paramsView.then (second graphCode (prodCode vectorCode vectorCode))
abbrev paramsFields := paramsTail.then (first vectorCode vectorCode)
abbrev paramsU := paramsTail.then (second vectorCode vectorCode)
abbrev paramsN : Realizes paramsCode natCode (fun p => p.graph.n) := paramsGraph.then numVertices
abbrev paramsM : Realizes paramsCode natCode (fun p => p.graph.m) := paramsGraph.then numEdges
private instance poly_paramsN : PolyTime paramsN := by
  unfold paramsN
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · unfold numVertices
    apply poly_then

private instance poly_paramsM : PolyTime paramsM := by
  unfold paramsM
  apply poly_then

def paramsField (k : ℕ) := ((constant paramsCode natCode k).both paramsFields).then (getD ratCode 0)
instance poly_paramsField (k : ℕ) : PolyTime (paramsField k) := by unfold paramsField;apply poly_then
abbrev paramsS : Realizes paramsCode ratCode Params.s := paramsField 0
abbrev paramsK : Realizes paramsCode ratCode Params.κ := paramsField 1
abbrev paramsT : Realizes paramsCode ratCode Params.t := paramsField 2
abbrev paramsQ : Realizes paramsCode ratCode Params.q := paramsField 3
abbrev paramsE : Realizes paramsCode ratCode Params.ε := paramsField 4
abbrev paramsDim := (paramsN.both paramsM).then dimensionProgram

structure Point where
  p : Params
  v : Fin (dimension p.graph.n p.graph.m) → ℚ

def Point.data (a : Point) := (a.p,List.ofFn a.v)
def pointCode (a : Point) : Word := prodCode paramsCode vectorCode a.data
abbrev pointView : Realizes pointCode (prodCode paramsCode vectorCode) Point.data :=
  (identity (prodCode paramsCode vectorCode)).reindex pointCode Point.data (fun _ => rfl)
private instance poly_pointView : PolyTime pointView := by
  unfold pointView
  apply poly_reindex

abbrev pointParams : Realizes pointCode paramsCode Point.p := pointView.then (first paramsCode vectorCode)
private instance poly_pointParams : PolyTime pointParams := by
  unfold pointParams
  apply poly_then

abbrev pointVector := pointView.then (second paramsCode vectorCode)
abbrev pointGraph : Realizes pointCode graphCode (fun a => a.p.graph) := pointParams.then paramsGraph
abbrev pointN : Realizes pointCode natCode (fun a => a.p.graph.n) := pointParams.then paramsN
abbrev pointM : Realizes pointCode natCode (fun a => a.p.graph.m) := pointParams.then paramsM
abbrev pointS : Realizes pointCode ratCode (fun a => a.p.s) := pointParams.then paramsS
abbrev pointK : Realizes pointCode ratCode (fun a => a.p.κ) := pointParams.then paramsK
abbrev pointT : Realizes pointCode ratCode (fun a => a.p.t) := pointParams.then paramsT
abbrev pointQ : Realizes pointCode ratCode (fun a => a.p.q) := pointParams.then paramsQ
abbrev pointE : Realizes pointCode ratCode (fun a => a.p.ε) := pointParams.then paramsE
abbrev pointU := pointParams.then paramsU
abbrev pointDim := pointParams.then paramsDim

def parsePoint (a : Params×List ℚ) : Point := ⟨a.1,fun i => a.2.getD i.val 0⟩
def pointParser : Realizes (prodCode paramsCode vectorCode) pointCode parsePoint :=
  let a := first paramsCode vectorCode
  let vs := second paramsCode vectorCode
  let base := first (prodCode paramsCode vectorCode) natCode
  let idx := second (prodCode paramsCode vectorCode) natCode
  let val := (idx.both (base.then vs)).then (getD ratCode 0)
  (a.both ((((identity (prodCode paramsCode vectorCode)).both (a.then paramsDim)).then val.tabulate))).changeOutput
    pointCode parsePoint (by
      intro a
      change prodCode paramsCode vectorCode (a.1,(List.range _).map _)=
        prodCode paramsCode vectorCode (a.1,List.ofFn _)
      rw [range_map_fin]
      rfl)
instance poly_pointParser : PolyTime pointParser := by
  have : PolyTime paramsDim := by unfold paramsDim; apply poly_then
  unfold pointParser
  apply poly_changeOutput
lemma parsePoint_ofFn (p : Params) (v : Fin (dimension p.graph.n p.graph.m) → ℚ) :
    parsePoint (p,List.ofFn v)=⟨p,v⟩ := by
  unfold parsePoint
  congr 1
  funext i
  exact getD_ofFn v i 0

variable {α : Type*} {ea : α → Word} {p : α → Point}
def coordinate (rp : Realizes ea pointCode p)
    (i : (a : α) → Fin (dimension (p a).p.graph.n (p a).p.graph.m))
    (ri : Realizes ea natCode (fun a => (i a).val)) :
    Realizes ea ratCode (fun a => (p a).v (i a)) :=
  ((ri.both (rp.then pointVector)).then (getD ratCode 0)).congr
    (fun a => getD_ofFn (p a).v (i a) 0)
instance poly_coordinate (rp : Realizes ea pointCode p)
    (i : (a : α) → Fin (dimension (p a).p.graph.n (p a).p.graph.m))
    (ri : Realizes ea natCode (fun a => (i a).val)) [PolyTime rp] [PolyTime ri] :
    PolyTime (coordinate rp i ri) := by unfold coordinate;apply poly_congr

def rawPoint : Realizes pointCode matrixObjectCode
    (fun a => ⟨a.p.graph.n,rawMatrix a.v⟩) :=
  (pointN.both ((((pointN.both pointM).both pointVector).then raw))).changeOutput
    matrixObjectCode (fun a => ⟨a.p.graph.n,rawMatrix a.v⟩) (by
      intro a
      change prodCode natCode matrixCode (a.p.graph.n,
        (List.range a.p.graph.n).map (fun i => (List.range a.p.graph.n).map
          (fun j => (List.ofFn a.v).getD (j+a.p.graph.n*i) 0)))=_
      rw [raw_data]
      rfl)
instance poly_rawPoint : PolyTime rawPoint := by
  have : PolyTime pointN := by unfold pointN; apply poly_then
  have : PolyTime pointM := by unfold pointM; apply poly_then
  unfold rawPoint
  apply poly_changeOutput
abbrev responsePoint := rawPoint.then GraphStack.response
abbrev lapPoint := pointGraph.then laplacian

def differenceVector {α : Type*} {ea : α → Word} {d : α → ℕ}
    (rn : Realizes ea natCode d) (i j : (a : α) → Fin (d a))
    (ri : Realizes ea natCode (fun a => (i a).val))
    (rj : Realizes ea natCode (fun a => (j a).val)) :
    Realizes ea vectorCode (fun a => List.ofFn (qdiff (i a) (j a))) :=
  ((((rn.both ri).then basisVector).both ((rn.both rj).then basisVector)).then vectorSub).congr (by
    intro a
    rw [basis_data,basis_data]
    exact vectorSub_data _ _)
instance poly_differenceVector {α : Type*} {ea : α → Word} {d : α → ℕ}
    (rn : Realizes ea natCode d) (i j : (a : α) → Fin (d a))
    (ri : Realizes ea natCode (fun a => (i a).val))
    (rj : Realizes ea natCode (fun a => (j a).val))
    [PolyTime rn] [PolyTime ri] [PolyTime rj] : PolyTime (differenceVector rn i j ri rj) := by
  unfold differenceVector;infer_instance
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI

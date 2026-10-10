import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialVariance
import OAI.Combinatorics.ThinTrees.Pencil.Parameters
import OAI.Combinatorics.ThinTrees.Pencil.Realization

namespace OAI

/-! Search realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

abbrev graphDim := (numVertices.both numEdges).then dimensionProgram
abbrev graphSizeProgram := ((numVertices.then natToRat).add (numEdges.then natToRat)).add
  (constant graphCode ratCode 2)
def graphRadius : Realizes graphCode ratCode (fun G => radiusQ G.n G.m) :=
  ((constant graphCode ratCode 1).div (graphSizeProgram.pow 50)).congr (by
    intro G; simp only [radiusQ,_root_.zpow_neg,one_div];rfl)
instance poly_graphRadius : PolyTime graphRadius := by unfold graphRadius;infer_instance

def graphBound : Realizes graphCode ratCode (fun G => boundQ G.n G.m) :=
  ((constant graphCode ratCode 6).mul graphSizeProgram).mul
    ((graphDim.then natToRat).add (constant graphCode ratCode 1))
instance poly_graphBound : PolyTime graphBound := by
  unfold graphBound
  refine @poly_mul _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_add _ _ _ _ _ _ ?_ ?_
    · apply poly_then
    · infer_instance

def graphZeros : Realizes graphCode vectorCode (fun G => List.ofFn (0 : Fin (dimension G.n G.m) → ℚ)) :=
  (((constant graphCode ratCode 0).both graphDim).then (replicateList ratCode)).congr
    (by
      intro G
      change List.replicate (dimension G.n G.m) 0 = List.ofFn (fun _ : Fin (dimension G.n G.m) => (0 : ℚ))
      rw [List.ofFn_const])
instance poly_graphZeros : PolyTime graphZeros := by unfold graphZeros;infer_instance

def Params.searchState (p : Params) : SearchState :=
  ⟨dimension p.graph.n p.graph.m,order p.graph.n p.graph.m,p.pencil,
    radiusQ p.graph.n p.graph.m,boundQ p.graph.n p.graph.m,0⟩

def initializeSearch : Realizes paramsCode searchStateCode Params.searchState :=
  (buildPencil.both
    (((paramsGraph.then graphRadius).both (paramsGraph.then graphBound)).both
      (paramsGraph.then graphZeros))).changeOutput searchStateCode Params.searchState (fun _ => rfl)
instance poly_initializeSearch : PolyTime initializeSearch := by unfold initializeSearch; apply poly_changeOutput

def solvePencil : Realizes paramsCode vectorCode (fun p =>
    List.ofFn (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0)) :=
  initializeSearch.then CurrentKS.Realization.search

lemma isPoly_graph_n : IsPoly (fun G => (graphCode G).length) Graph.n := by
  have h := (RunsPoly.of_poly numVertices id (isPoly_self (fun G => (graphCode G).length))).output
  simpa only [id_eq,natCode,List.length_replicate,Graph.data] using h
lemma isPoly_graph_m : IsPoly (fun G => (graphCode G).length) Graph.m := by
  have h := (RunsPoly.of_poly numEdges id (isPoly_self (fun G => (graphCode G).length))).output
  simpa only [id_eq,natCode,List.length_replicate,Graph.data] using h
lemma isPoly_graph_fuel : IsPoly (fun G => (graphCode G).length)
    (fun G => CurrentKS.RationalSDP.searchFuel (dimension G.n G.m) (radiusQ G.n G.m) (boundQ G.n G.m)) := by
  have hP := (isPoly_graph_n.add isPoly_graph_m).add (isPoly_const _ 2)
  exact (((isPoly_const _ 2304).mul (hP.pow 114)).add (isPoly_const _ 1)).mono
    (fun G => search_fuel_bound G.n G.m)

instance poly_solvePencil : PolyTime solvePencil := by
  let L := fun p => (paramsCode p).length
  have hi := RunsPoly.of_poly initializeSearch id (isPoly_self L)
  have hg := RunsPoly.of_poly paramsGraph id (isPoly_self L)
  obtain ⟨q,hq⟩ := isPoly_graph_fuel
  have hf := (hg.output.eval q).mono (fun p => hq p.graph)
  exact ⟨(hi.then (runsPoly_search Params.searchState hi.output hf)).cost⟩

def gridStep := graphRadius.div ((graphDim.then natToRat).add (constant graphCode ratCode 1))
instance poly_gridStep : PolyTime gridStep := by unfold gridStep;infer_instance

def gridMesh := (gridStep.pow 2).div
  (((constant graphCode ratCode 16).mul ((graphDim.then natToRat).add (constant graphCode ratCode 1))).mul
    ((graphBound.add gridStep).add (constant graphCode ratCode 1)))
instance poly_gridMesh : PolyTime gridMesh := by unfold gridMesh;infer_instance

lemma search_parts_bound : ∃q : NaturalPolynomial, ∀p : Params, ∀i,
    QParts (q.eval (graphCode p.graph).length)
      (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0 i) := by
  have hc := (RunsPoly.of_poly (gridStep.both gridMesh) id
    (isPoly_self (fun G => (graphCode G).length))).output
  obtain ⟨b,hb⟩ := hc
  obtain ⟨f,hf⟩ := isPoly_graph_fuel
  refine ⟨3*b+f+1,?_⟩
  intro p i
  let H := b.eval (graphCode p.graph).length
  have hstep : QParts H (CurrentKS.RationalSDP.searchStep (dimension p.graph.n p.graph.m) (radiusQ p.graph.n p.graph.m)) :=
    (qparts_length _).mono ((le_prodCode_left _).trans (hb p.graph))
  have hmesh : QParts H (CurrentKS.RationalSDP.searchMesh (dimension p.graph.n p.graph.m) (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m)) :=
    (qparts_length _).mono ((le_prodCode_right _).trans (hb p.graph))
  apply (pencil_iterate_parts p.pencil _ _ 0 hstep hmesh (fun _ => qparts_zero H) _ i).mono
  change 3*H+_+1 ≤ 3*H+f.eval _+1
  exact Nat.add_le_add_right (Nat.add_le_add_left (hf p.graph) _) _

lemma search_output_bound : ∃q : NaturalPolynomial, ∀p : Params,
    (vectorCode (List.ofFn (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0))).length ≤
      q.eval (graphCode p.graph).length := by
  obtain ⟨b,hb⟩ := search_parts_bound
  obtain ⟨d,hd⟩ := (RunsPoly.of_poly graphDim id
    (isPoly_self (fun G => (graphCode G).length))).output
  refine ⟨d*(2*(4*b+7)+1),?_⟩
  intro p
  have h := listCode_length_bound (List.ofFn
    (p.pencil.search (radiusQ p.graph.n p.graph.m) (boundQ p.graph.n p.graph.m) 0))
      (4*b.eval (graphCode p.graph).length+7) (by
        intro q hq; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq;exact (hb p i).length)
  rw [List.length_ofFn] at h
  exact h.trans (Nat.mul_le_mul_right _ (by simpa only [id_eq,natCode,List.length_replicate,Graph.data] using hd p.graph))
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI

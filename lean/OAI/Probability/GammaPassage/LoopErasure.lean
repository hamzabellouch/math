import OAI.Probability.FirstPassage.PassageTime
import OAI.Probability.FirstPassage.PathWitnesses
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Algebra.Order.BigOperators.Group.List
import Lean.Elab.Tactic.Omega

namespace OAI

namespace GammaFPP.LoopGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Undirected edge weights; the domain contains only actual edges. -/
abbrev Weights (G : SimpleGraph V) := G.edgeSet → ℝ

def edgeCost (w : Weights G) {x y : V} (h : G.Adj x y) : ℝ :=
  w ⟨s(x, y), h⟩

@[simp] theorem edgeCost_symm (w : Weights G) {x y : V} (h : G.Adj x y) :
    edgeCost w h.symm = edgeCost w h := by
  simp only [edgeCost, Sym2.eq_swap]

/-- Recursion counts repeated traversals with multiplicity. -/
def pathCost (w : Weights G) {x y : V} : G.Walk x y → ℝ
  | .nil => 0
  | .cons h p => edgeCost w h + pathCost w p

@[simp] theorem pathCost_nil (w : Weights G) (x : V) :
    pathCost w (SimpleGraph.Walk.nil : G.Walk x x) = 0 := rfl

@[simp] theorem pathCost_cons (w : Weights G) {x y z : V}
    (h : G.Adj x y) (p : G.Walk y z) :
    pathCost w (.cons h p) = edgeCost w h + pathCost w p := rfl

lemma pathCost_eq_darts_sum (w : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost w p = (p.darts.map (fun d => edgeCost w d.adj)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, edgeCost]

/-- Loop erasure does not increase a path's physical cost. -/
theorem bypass_cost_le [DecidableEq V] (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : pathCost w p.bypass ≤ pathCost w p := by
  rw [pathCost_eq_darts_sum, pathCost_eq_darts_sum]
  apply (p.darts_bypass_sublist_darts.map (fun d => edgeCost w d.adj)).sum_le_sum
  intro a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
  exact hw _

abbrev Vertex := ℤ × ℤ

def lattice : SimpleGraph Vertex where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨by intros x y h; simpa only [abs_sub_comm] using h⟩
  loopless := ⟨by intro x; simp⟩

abbrev Edge := lattice.edgeSet
abbrev Environment := Weights lattice

end GammaFPP.LoopGraph

namespace GammaFPP.LoopErase
open PlanarFPP

lemma companion_adj_step (p : Vertex) (d : Step) :
    GammaFPP.LoopGraph.lattice.Adj p (p+d.delta) := by
  cases d <;> simp [GammaFPP.LoopGraph.lattice, Step.delta]

lemma companion_adj_iff (p q : Vertex) :
    GammaFPP.LoopGraph.lattice.Adj p q ↔ ∃ d : Step, q=p+d.delta := by
  constructor
  · intro h
    change |p.1-q.1|+|p.2-q.2|=1 at h
    have hor : (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1-1 ∧ q.2=p.2) ∨
        (q.1=p.1 ∧ q.2=p.2+1) ∨ (q.1=p.1 ∧ q.2=p.2-1) := by
      simp only [abs_eq_max_neg] at h
      omega
    rcases hor with h | h | h | h
    · exact ⟨.east, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.west, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.north, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.south, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
  · rintro ⟨d,rfl⟩
    exact companion_adj_step p d

def companionEdge (e : Edge) : GammaFPP.LoopGraph.Edge :=
  if e.2 = true then ⟨s(e.1,e.1+Step.north.delta), companion_adj_step _ _⟩
  else ⟨s(e.1,e.1+Step.east.delta), companion_adj_step _ _⟩

lemma companionEdge_step (p : Vertex) (d : Step) :
    companionEdge (d.edge p) = ⟨s(p,p+d.delta),companion_adj_step p d⟩ := by
  apply Subtype.ext
  cases d <;> simp [companionEdge,Step.edge,Step.delta,Prod.ext_iff]

lemma companionEdge_injective : Function.Injective companionEdge := by
  rintro ⟨⟨px,py⟩,b⟩ ⟨⟨qx,qy⟩,c⟩ h
  have he := congrArg Subtype.val h
  cases b <;> cases c <;>
    simp [companionEdge,Step.delta,Prod.ext_iff] at he ⊢ <;>
    rcases he with h | h <;> omega

lemma companionEdge_surjective : Function.Surjective companionEdge := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p q).mp he
    exact ⟨d.edge p,companionEdge_step p d⟩

noncomputable def companionEdgeEquiv : Edge ≃ GammaFPP.LoopGraph.Edge :=
  Equiv.ofBijective companionEdge ⟨companionEdge_injective,companionEdge_surjective⟩

noncomputable def companionWeights (w : Edge → ℝ) : GammaFPP.LoopGraph.Environment :=
  fun e => w (companionEdgeEquiv.symm e)

@[simp] lemma companionWeights_edge (w : Edge → ℝ) (e : Edge) :
    companionWeights w (companionEdge e)=w e := by
  change w (companionEdgeEquiv.symm (companionEdgeEquiv e))=w e
  rw [companionEdgeEquiv.symm_apply_apply]

@[simp] lemma companion_pathCost_copy (w : GammaFPP.LoopGraph.Environment)
    {p q p' q' : Vertex} (walk : GammaFPP.LoopGraph.lattice.Walk p q) (hp : p=p') (hq : q=q') :
    GammaFPP.LoopGraph.pathCost w (walk.copy hp hq) = GammaFPP.LoopGraph.pathCost w walk := by
  subst p'; subst q'; rfl

lemma steps_companion_walk (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : GammaFPP.LoopGraph.lattice.Walk p (p+displacement ds),
      GammaFPP.LoopGraph.pathCost (companionWeights w) walk = pathCost w p ds := by
  induction ds generalizing p with
  | nil =>
    refine ⟨(SimpleGraph.Walk.nil : GammaFPP.LoopGraph.lattice.Walk p p).copy rfl (by simp),?_⟩
    rw [companion_pathCost_copy]
    rfl
  | cons d ds ih =>
    obtain ⟨walk,hw⟩ := ih (p+d.delta)
    have he : (p+d.delta)+displacement ds = p+displacement (d::ds) := by
      simp [add_assoc]
    refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he,?_⟩
    simp only [companion_pathCost_copy, GammaFPP.LoopGraph.pathCost_cons, GammaFPP.LoopGraph.edgeCost, pathCost, hw]
    rw [← companionEdge_step,companionWeights_edge]

/-- The walk-to-step bridge preserves the ordered list of unoriented edges,
in addition to endpoints and traversal-counted cost. -/
lemma companion_walk_steps_edges (w : Edge → ℝ) {p q : Vertex}
    (walk : GammaFPP.LoopGraph.lattice.Walk p q) :
    ∃ ds : List Step, p+displacement ds=q ∧
      pathCost w p ds=GammaFPP.LoopGraph.pathCost (companionWeights w) walk ∧
      ((trace p ds).map (fun t => (companionEdge (traversalEdge t)).val))=walk.edges := by
  induction walk with
  | nil => exact ⟨[],by simp,rfl,rfl⟩
  | @cons p u q hadj walk ih =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p u).mp hadj
    obtain ⟨ds,he,hc,hedges⟩ := ih
    refine ⟨d::ds,by simpa [add_assoc] using he,?_,?_⟩
    · simp only [pathCost,GammaFPP.LoopGraph.pathCost_cons,GammaFPP.LoopGraph.edgeCost,hc]
      rw [← companionEdge_step,companionWeights_edge]
    · simp only [trace,List.map_cons,traversalEdge,companionEdge_step,SimpleGraph.Walk.edges_cons]
      simpa only [traversalEdge,companionEdge_step] using congrArg (List.cons s(p,p+d.delta)) hedges

/-- Loop erasure in the exact original path model, for arbitrary endpoints
and nonnegative real weights. It never increases cost. -/
theorem erase_path_loops (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p : Vertex) (ds : List Step) :
    ∃ es : List Step, displacement es=displacement ds ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ pathCost w p ds := by
  obtain ⟨walk,hcost⟩ := steps_companion_walk w p ds
  obtain ⟨es,hend,hc,he⟩ := companion_walk_steps_edges w walk.bypass
  have hn := walk.bypass_isPath.isTrail.edges_nodup
  rw [← he] at hn
  have hn' : (((trace p es).map traversalEdge).map (fun e => (companionEdge e).val)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using hn
  refine ⟨es,add_left_cancel hend,List.Nodup.of_map _ hn',?_⟩
  rw [hc,← hcost]
  exact GammaFPP.LoopGraph.bypass_cost_le (companionWeights w) (fun e => hw _) walk

/-- Near-optimal paths with simple physical-edge traces, at every pair of
lattice endpoints and every positive approximation error. -/
theorem exists_near_optimal_simple_path (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p+displacement ds=q ∧
      ((trace p ds).map traversalEdge).Nodup ∧
      passageTime w p q ≤ pathCost w p ds ∧ pathCost w p ds < passageTime w p q+ε := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  obtain ⟨es,he,hs,hc⟩ := erase_path_loops w hw p ds
  have he' : p+displacement es=q := by rw [he,hend]
  exact ⟨es,he',hs,passageTime_le_cost w hw p q es he',hc.trans_lt hcost⟩

end GammaFPP.LoopErase

end OAI

import OAI.Probability.FirstPassage.ContiguousWitnesses
import OAI.Probability.FirstPassage.CompanionModel
import OAI.Probability.LatticePassage.Geodesic

namespace OAI

namespace PlanarFPP

lemma companion_walk_steps_edges (w : Edge → ℝ) {p q : Vertex}
    (walk : CompanionFPP.lattice.Walk p q) :
    ∃ ds : List Step, p+displacement ds=q ∧
      pathCost w p ds=CompanionFPP.pathCost (companionWeights w) walk ∧
      ((trace p ds).map (fun t => (companionEdge (traversalEdge t)).val))=walk.edges := by
  induction walk with
  | nil => exact ⟨[],by simp,rfl,rfl⟩
  | @cons p u q hadj walk ih =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p u).mp hadj
    obtain ⟨ds,he,hc,hedges⟩ := ih
    refine ⟨d::ds,by simpa [add_assoc] using he,?_,?_⟩
    · simp only [pathCost,CompanionFPP.pathCost_cons,CompanionFPP.edgeCost,hc]
      rw [← companionEdge_step,companionWeights_edge]
    · simp only [trace,List.map_cons,traversalEdge,companionEdge_step,SimpleGraph.Walk.edges_cons]
      simpa only [traversalEdge,companionEdge_step] using congrArg (List.cons s(p,p+d.delta)) hedges

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
  exact CompanionFPP.bypass_cost_le (companionWeights w) (fun e => hw _) walk

theorem exists_near_optimal_simple_path (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p+displacement ds=q ∧
      ((trace p ds).map traversalEdge).Nodup ∧
      passageTime w p q ≤ pathCost w p ds ∧ pathCost w p ds < passageTime w p q+ε := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  obtain ⟨es,he,hs,hc⟩ := erase_path_loops w hw p ds
  have he' : p+displacement es=q := by rw [he,hend]
  exact ⟨es,he',hs,passageTime_le_cost w hw p q es he',hc.trans_lt hcost⟩

end PlanarFPP

end OAI

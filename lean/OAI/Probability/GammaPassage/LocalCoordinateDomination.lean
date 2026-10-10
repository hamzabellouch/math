import OAI.Probability.GammaPassage.LocalTrailPassage

namespace OAI

namespace GammaFPP
open PlanarFPP

lemma coordinatePath_length_eq_distance (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

namespace LoopErase
lemma steps_companion_walk_length (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : LoopGraph.lattice.Walk p (p + displacement ds),
      LoopGraph.pathCost (companionWeights w) walk = pathCost w p ds ∧
      walk.length = ds.length := by
  induction ds generalizing p with
  | nil =>
      refine ⟨(SimpleGraph.Walk.nil : LoopGraph.lattice.Walk p p).copy rfl (by simp), ?_, ?_⟩
      · rw [companion_pathCost_copy]; rfl
      · rw [SimpleGraph.Walk.length_copy]
        rfl
  | cons d ds ih =>
      obtain ⟨walk, hw, hl⟩ := ih (p + d.delta)
      have he : (p + d.delta) + displacement ds = p + displacement (d :: ds) := by
        simp [add_assoc]
      refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he, ?_, ?_⟩
      · simp only [companion_pathCost_copy, LoopGraph.pathCost_cons, LoopGraph.edgeCost,
          pathCost, hw]
        rw [← companionEdge_step, companionWeights_edge]
      · simp [hl]

lemma erase_path_loops_length (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) :
    ∃ es : List Step, p + displacement es = p + displacement ds ∧
      ((trace p es).map traversalEdge).Nodup ∧ es.length ≤ ds.length ∧
      pathCost w p es ≤ pathCost w p ds := by
  obtain ⟨walk, hc, hl⟩ := steps_companion_walk_length w p ds
  obtain ⟨es, he, hcost, hedges⟩ := companion_walk_steps_edges w walk.bypass
  have hn := walk.bypass_isPath.isTrail.edges_nodup
  rw [← hedges] at hn
  have hn' : (((trace p es).map traversalEdge).map (fun e => (companionEdge e).val)).Nodup := by
    simpa only [List.map_map, Function.comp_def] using hn
  have hlen : es.length = walk.bypass.length := by
    have hh := congrArg List.length hedges
    have htrace : (trace p es).length = es.length := by
      simpa only [List.length_map] using trace_edge_length p es
    simpa only [List.length_map, SimpleGraph.Walk.length_edges, htrace] using hh
  refine ⟨es, he, List.Nodup.of_map _ hn', ?_, ?_⟩
  · rw [hlen, ← hl]
    exact walk.length_bypass_le_length
  · rw [hcost, ← hc]
    exact LoopGraph.bypass_cost_le (companionWeights w) (fun e => hw _) walk
end LoopErase

lemma FiniteLocal.passageTime_le_coordinatePath (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    FiniteLocal.passageTime w p q R ≤ pathCost w p (coordinatePath p q) := by
  obtain ⟨es, he, hn, hl, hc⟩ := LoopErase.erase_path_loops_length w hw p (coordinatePath p q)
  have hend : p + displacement es = q := he.trans (coordinatePath_endpoint p q)
  have hlen : es.length < R := hl.trans_lt (by rwa [coordinatePath_length_eq_distance])
  exact (FiniteLocal.passageTime_le_candidate w p q R es
    ((FiniteLocal.mem_candidates p q R es).mpr ⟨hend, hn, hlen⟩)).trans hc
end GammaFPP

end OAI

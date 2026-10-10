import OAI.Combinatorics.TriangleFace.Labels
import OAI.Combinatorics.TriangleFace.AffineMaps

namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

omit [Fintype V] [Fintype E] in
theorem expandMatching_indicator (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) (M : G.Matching) :
    (triangleExpansion G c v).indicator (expandMatching G c v M) = localExtension G c v hc (G.indicator M) := by
  ext e
  rcases e with e | i
  · simp [LooplessGraph.indicator,expandMatching,expandEdges,localExtension]
  · have hh : c (incidentChoice G M v) = i ↔ localEdge G c v hc i ∈ M.val := by
      constructor
      · intro h
        rw [← eq_localEdge G c v hc (incidentChoice_spec G M v).2 h]
        exact (incidentChoice_spec G M v).1
      · intro h
        rw [← eq_incidentChoice G M v h (localEdge_spec G c v hc i).1]
        exact (localEdge_spec G c v hc i).2
    simp only [LooplessGraph.indicator,expandMatching,expandEdges,Finset.inr_mem_disjSum,
      Finset.mem_singleton,localExtension,LinearMap.coe_mk,AddHom.coe_mk,Sum.elim_inr]
    simp only [eq_comm (a := i) (b := c (incidentChoice G M v)),hh]

theorem expanded_push_mean {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) (q : G.Matching → ℝ) :
    (triangleExpansion G c v).mean (fiberMass q (expandMatching G c v)) =
      localExtension G c v hc (G.mean q) := by
  ext e
  rw [LooplessGraph.mean,fiberMass_expect]
  simp_rw [expandMatching_indicator G c v hc]
  rcases e with e | i <;> rfl

theorem expanded_push_feasible (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) {x : E → ℝ} {q : G.Matching → ℝ}
    (hq : q ∈ G.feasibleLaws x) :
    fiberMass q (expandMatching G c v) ∈ (triangleExpansion G c v).feasibleLaws (localExtension G c v hc x) := by
  exact ⟨fiberMass_mem_simplex hq.1 _,by rw [expanded_push_mean G c v hc,hq.2]⟩

theorem expansion_image_eq (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) :
    localExtension G c v hc '' G.polytope =
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨q,hq⟩ := (G.mem_polytope_iff x).mp hx
    refine ⟨((triangleExpansion G c v).mem_polytope_iff _).mpr
      ⟨_,expanded_push_feasible G c v hc hq⟩,?_⟩
    rw [expanded_cutMass]
    exact (G.polytope_subset_constraintPolytope hx).2.1 v
  · rintro ⟨hy,ht⟩
    obtain ⟨p,hp⟩ := ((triangleExpansion G c v).mem_polytope_iff y).mp hy
    have ht' : (triangleExpansion G c v).cutMass ((triangleExpansion G c v).mean p) (triangleVertices v) = 1 := hp.2.symm ▸ ht
    obtain ⟨heq,hq⟩ := expanded_pull_simplex G c v hp.1 ht'
    refine ⟨_,G.mean_mem_polytope hq,?_⟩
    rw [← expanded_push_mean,← heq,hp.2]

theorem expansion_image_extreme (G : LooplessGraph V E) (c : E → Fin 3)
    (v : V) (hc : LocalLabels G v c) :
    IsExtreme ℝ (triangleExpansion G c v).polytope (localExtension G c v hc '' G.polytope) := by
  rw [expansion_image_eq]
  refine ⟨fun _ h => h.1, ?_⟩
  intro y hy z hz w hw hseg
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hseg
  refine ⟨hy,?_⟩
  have heq := hw.2
  rw [LooplessGraph.cutMass_linear] at heq
  have hyl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hy).2.2 _ (triangleVertices_odd v)
  have hzl := ((triangleExpansion G c v).polytope_subset_constraintPolytope hz).2.2 _ (triangleVertices_odd v)
  apply le_antisymm _ hyl
  by_contra! hn
  have hpos := mul_pos ha (sub_pos.mpr hn)
  have hnonneg := mul_nonneg hb.le (sub_nonneg.mpr hzl)
  nlinarith

end TriangleFace198
end

end OAI

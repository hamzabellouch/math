import OAI.Combinatorics.TriangleFace.Model

namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem labels_of_degree_three {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3) :
    ∃ c : E → Fin 3, LocalLabels G v c := by
  classical
  let q : {e : E // G.Incident v e} ≃ Fin 3 := Fintype.equivFinOfCardEq hdeg
  let c : E → Fin 3 := fun e => if h : G.Incident v e then q ⟨e,h⟩ else 0
  refine ⟨c, ?_⟩
  intro i
  refine ⟨(q.symm i).val, ⟨(q.symm i).property, ?_⟩, ?_⟩
  · simp [c, (q.symm i).property]
  · intro e he
    have hq : q ⟨e,he.1⟩ = i := by simpa [c,he.1] using he.2
    exact congrArg Subtype.val (q.injective (hq.trans (q.apply_symm_apply i).symm))

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem localEdge_spec (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) :
    G.Incident v (localEdge G c v hc i) ∧ c (localEdge G c v hc i) = i :=
  (Classical.choose_spec (hc i)).1

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem eq_localEdge (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) {e : E} {i : Fin 3}
    (he : G.Incident v e) (hi : c e = i) : e = localEdge G c v hc i :=
  (Classical.choose_spec (hc i)).2 e ⟨he,hi⟩

end TriangleFace198
end

end OAI

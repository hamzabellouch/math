import OAI.Combinatorics.Ramsey.CycleClique.Construction.NormalizedIncident
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalRepresentatives

namespace OAI

/-! Normalizing a raw orientation preserves its ground, amount, optimality,
and every representative, including its isolated clique vertices. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem normalize_ground (U : RawPathSystem G Q) :
    U.normalize.ground = Q ∪ U.vertices := by
  classical
  have he := normalizeChains_outside_vertices U.chains U.paths U.disjoint U.endpoints U.no_clique_steps
  change U.normalize.vertices \ Q = U.vertices \ Q at he
  ext x
  by_cases hx : x ∈ Q
  · simp [ExpandedPathSystem.ground, hx]
  · have hh := Finset.ext_iff.mp he x
    simpa [ExpandedPathSystem.ground, hx] using hh

theorem normalize_representative_mem (U : RawPathSystem G Q) {x : V}
    (hx : x ∈ U.representatives) : x ∈ U.normalize.representativeFinset := by
  classical
  obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hr
  have hxl : x ∈ l := (chainRepresentatives_sublist l).subset hxr
  by_cases hlen : 3 ≤ l.length
  · have hlE : l ∈ U.normalize.chains := List.mem_filter.mpr ⟨hl, by simpa using hlen⟩
    apply List.mem_toFinset.mpr
    apply List.mem_flatten.mpr
    refine ⟨chainRepresentatives Q l, ?_, hxr⟩
    apply List.mem_map.mpr
    exact ⟨l, List.mem_append_left _ hlE, rfl⟩
  · have hxQ : x ∈ Q := short_chain_in_clique (U.endpoints l hl)
      (U.no_clique_steps l hl) (by omega) x hxl
    have hxnot : x ∉ U.normalize.vertices := by
      intro hxE
      obtain ⟨m, hm, hxm⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hxE)
      have hmU : m ∈ U.chains := (List.mem_filter.mp hm).1
      have hmLen : 3 ≤ m.length := by simpa using (List.mem_filter.mp hm).2
      have hne : l ≠ m := by intro he; subst m; exact hlen hmLen
      exact List.disjoint_left.mp (U.disjoint_of_mem hl hmU hne) hxl hxm
    apply List.mem_toFinset.mpr
    apply List.mem_flatten.mpr
    refine ⟨chainRepresentatives Q [x], ?_, by simp [chainRepresentatives]⟩
    apply List.mem_map.mpr
    refine ⟨[x], ?_, rfl⟩
    change [x] ∈ U.normalize.chains ++ (Q \ U.normalize.toRaw.vertices).toList.map (fun v => [v])
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨x, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hxQ, hxnot⟩), rfl⟩

end CycleClique.Construction.RawPathSystem

namespace CycleClique.Construction.ExpandedPathSystem

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V} {S : ExpandedPathSystem G Q}

theorem IsOptimal.of_amount_count {k : ℕ} (hopt : S.IsOptimal k)
    (T : ExpandedPathSystem G Q) (ha : T.amount = S.amount)
    (he : T.assignedCount = S.assignedCount) : T.IsOptimal k := by
  refine ⟨by simpa only [ha] using hopt.budget, ?_, ?_⟩
  · intro U hU
    simpa only [ha] using hopt.maximal U hU
  · intro U hU
    rw [he]
    exact hopt.minimal U (hU.trans ha)

end CycleClique.Construction.ExpandedPathSystem

end OAI

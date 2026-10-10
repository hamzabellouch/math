import OAI.Combinatorics.Ryser.Construction.Hypergraph

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem ordinaryVertex_mem_ordinaryEdge_iff (data : ConfigurationData k F G)
    (x : Point F) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ ordinaryEdge data x ↔ Incidence x ell := by
  constructor
  · intro hv
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hv
    have hline : lineThrough d x = ell := Sum.inl.inj hd
    rw [← hline]
    exact incidence_lineThrough d x
  · intro hinc
    rw [eq_lineThrough_of_incidence hinc]
    exact ordinaryVertex_mem_ordinaryEdge data x ell.1

theorem ordinaryVertex_mem_exceptionalEdge_iff (data : ConfigurationData k F G)
    (i : G) (w : Point k) (ell : AffineLine F) :
    ordinaryVertex data ell ∈ exceptionalEdge data i w ↔
      ell.1 ∉ data.altered i ∧ Incidence (data.base i w) ell := by
  rw [mem_exceptionalEdge_iff data i w, vertexPart_ordinaryVertex]
  by_cases hd : ell.1 ∈ data.altered i
  · rw [exceptionalVertex_of_mem data i w ell.1 hd]
    constructor
    · intro hlabel
      simp [ordinaryVertex, specialVertex] at hlabel
    · intro h
      exact False.elim (h.1 hd)
  · rw [exceptionalVertex_of_notMem data i w ell.1 hd]
    constructor
    · intro hlabel
      have hline : ell = lineThrough ell.1 (data.base i w) := Sum.inl.inj hlabel
      exact ⟨hd, (congrArg Prod.snd hline).symm⟩
    · rintro ⟨_, hinc⟩
      exact congrArg (ordinaryVertex data) (eq_lineThrough_of_incidence hinc)

theorem specialVertex_mem_exceptionalEdge_iff (data : ConfigurationData k F G)
    (i : G) (w : Point k)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    specialVertex data i d c ∈ exceptionalEdge data i w ↔
      Incidence (data.transform w) (some (data.inverseSlope i d), c) := by
  rw [mem_exceptionalEdge_iff data i w, vertexPart_specialVertex,
    exceptionalVertex_of_mem data i w d.val d.property]
  change specialVertex data i d c =
      specialVertex data i d
        (projection (some (data.inverseSlope i d)) (data.transform w)) ↔
    Incidence (data.transform w) (some (data.inverseSlope i d), c)
  constructor
  · intro hlabel
    have hc : c = projection (some (data.inverseSlope i d)) (data.transform w) :=
      congrArg
        (fun v : Σ j : G, {e : Direction F // e ∈ data.altered j} × k => v.2.2)
        (Sum.inr.inj hlabel)
    exact hc.symm
  · intro hinc
    change projection (some (data.inverseSlope i d)) (data.transform w) = c at hinc
    rw [hinc]

theorem specialVertex_notMem_exceptionalEdge_of_ne (data : ConfigurationData k F G)
    (i j : G) (hij : i ≠ j) (w : Point k)
    (d : {d : Direction F // d ∈ data.altered i}) (c : k) :
    specialVertex data i d c ∉ exceptionalEdge data j w := by
  intro hv
  have hlabel := (mem_exceptionalEdge_iff data j w _).mp hv
  rw [vertexPart_specialVertex] at hlabel
  by_cases hd : d.val ∈ data.altered j
  · rw [exceptionalVertex_of_mem data j w d.val hd] at hlabel
    exact hij (congrArg Sigma.fst (Sum.inr.inj hlabel))
  · rw [exceptionalVertex_of_notMem data j w d.val hd] at hlabel
    simp [ordinaryVertex, specialVertex] at hlabel

theorem specialVertex_notMem_ordinaryEdge (data : ConfigurationData k F G)
    (i : G) (d : {d : Direction F // d ∈ data.altered i}) (c : k) (x : Point F) :
    specialVertex data i d c ∉ ordinaryEdge data x := let _ := instFieldk; by
  intro hv
  obtain ⟨d', _, hlabel⟩ := Finset.mem_image.mp hv
  simp [ordinaryVertex, specialVertex] at hlabel

end RyserCoveringCounterexample.Construction

end OAI

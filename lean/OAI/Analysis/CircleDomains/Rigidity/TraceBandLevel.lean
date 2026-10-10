import OAI.Analysis.CircleDomains.Uniformization.BandLimits

namespace OAI

/-! At a point with a genuine limiting real trace, the entire circle
band is the single projected trace value. -/

open Set Filter
open scoped Topology

namespace CircleDomainRigidity

theorem circleBandGraph_of_trace
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [CompactSpace X] [T2Space X] {G : Set X} {u : X → ℝ} {M : ℝ}
    (hM : ∀x ∈ G, |u x| ≤ M) {x : X} (hx : x ∈ closure G) {v : ℝ}
    (htrace : Tendsto u (𝓝[G] x) (𝓝 v)) {t : AddCircle (1 : ℝ)} :
    (x, t) ∈ circleBandGraph G u ↔ (v : AddCircle (1 : ℝ)) = t := by
  let : NeBot (𝓝[G] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hband : ∀r : ℝ, (x, r) ∈ intervalFiberHull (clusterGraph G u) ↔ r = v := by
    intro r
    have he := intervalFiberHull_clusterGraph_eq_boundary_band hM hx
    have hr := Set.ext_iff.mp he r
    simpa only [mem_ofPred_eq, htrace.liminf_eq, htrace.limsup_eq, Icc_self,
      mem_singleton_iff] using hr
  constructor
  · rintro ⟨⟨y, r⟩, hr, heq⟩
    obtain ⟨rfl, ht⟩ := Prod.mk.inj heq
    rwa [(hband r).mp hr] at ht
  · intro ht
    exact ⟨(x, v), (hband v).mpr rfl, Prod.ext rfl ht⟩

end CircleDomainRigidity

end OAI

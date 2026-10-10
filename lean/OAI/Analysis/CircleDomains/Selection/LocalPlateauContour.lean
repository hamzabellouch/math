import OAI.Analysis.CircleDomains.Modulus.RealSourceBarriers

namespace OAI

/-! A local plateau admits a sufficiently deep genuine end contour that also avoids the fixed
compact target anchor. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

theorem exists_plateau_contour_avoiding_anchor
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (l : ℕ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (hone : ∀ x ∈ U ∩ d.source, d.coordinate l x = 1)
    {K : Set ℂ} (hK : IsCompact K) (hKA : ((↑) : ℂ → Sphere) '' K ⊆ extendAtInfinity A.function '' G) :
    ∃ k : ℕ,
      (∀ z ∈ frontier (jordanInterior ((A.cores k).disk (E.address k))),
        d.physical l (Complex.equivRealProdCLM z) = 1) ∧
      Disjoint K (closure (jordanInterior (A.contours k (E.address k)))) := by
  obtain ⟨n, _, hsource⟩ := E.exists_positive_level_in_neighborhood hπ hr hq hU hqU
  have htarget : (⋂ n, closedTerminalCap (A.contours n (E.address n))) ⊆
      (((↑) : ℂ → Sphere) '' K)ᶜ := by
    rw [← E.target]
    intro p hp hpK
    exact connectedComponentIn_subset _ _ hp (hKA hpK)
  obtain ⟨m, htargetm⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.cap_antitone
    (hK.image OnePoint.continuous_coe).isClosed.isOpen_compl htarget
  let k := max n m
  have hsourcek := (E.source_cap_antitone (le_max_left n m)).trans hsource
  have htargetk := (E.cap_antitone (le_max_right n m)).trans htargetm
  refine ⟨k, ?_, ?_⟩
  · intro z hz
    have hzG := (A.cores k).boundary_subset_domain (E.address k) ⟨z, hz, rfl⟩
    rw [d.pullback l z hzG]
    exact hone (π z) ⟨hsourcek ⟨z, frontier_subset_closure hz, rfl⟩, d.source_map z hzG⟩
  · apply Set.disjoint_left.mpr
    intro z hzK hzcap
    exact htargetk ⟨z, hzcap, rfl⟩ (mem_image_of_mem _ hzK)

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI

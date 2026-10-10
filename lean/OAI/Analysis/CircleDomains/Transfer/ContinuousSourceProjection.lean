import OAI.Analysis.CircleDomains.Transfer.SourceEndProjection

namespace OAI

/-! Nested matched caps prove continuity of the source quotient projection
at every complementary point, including nondegenerate target components. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε}
namespace AssignedRealModelLimit
variable (L : AssignedRealModelLimit M)

 theorem sourceProjection_continuous (hG : IsOpen G)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (hc : ∀ q p, p ∈ connectedComponentIn Gᶜ q → π p = π q) :
    Continuous (L.sourceProjection hG π) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ extendAtInfinity L.function '' G
  · obtain ⟨x, hx, rfl⟩ := hp
    have hi := continuousAt_conformal_invFunOn L.conformal.1 hG L.conformal.bijOn.injOn hx
    have hcont := hπ.continuousAt.comp hi
    have hval : L.sourceProjection hG π (extendAtInfinity L.function x) =
        π (invFunOn (extendAtInfinity L.function) G (extendAtInfinity L.function x)) := by
      simp only [sourceProjection, dite_eq_left (mem_image_of_mem _ hx)]
    change Tendsto (L.sourceProjection hG π) (𝓝 (extendAtInfinity L.function x))
      (𝓝 (L.sourceProjection hG π (extendAtInfinity L.function x)))
    rw [hval]
    apply hcont.congr'
    have hV := L.conformal.1.isOpen_image hG hG (Subset.refl G)
    filter_upwards [hV.mem_nhds (mem_image_of_mem _ hx)] with z hz
    simp only [sourceProjection, dite_eq_left hz, comp_apply]
  · let A := L.chosenSourceEnd hG p hp
    have hval : L.sourceProjection hG π p = π A.source := L.sourceProjection_off_image hG π hp
    change Tendsto (L.sourceProjection hG π) (𝓝 p) (𝓝 (L.sourceProjection hG π p))
    rw [hval]
    apply tendsto_nhds.mpr
    intro V hV hpV
    have hsub : connectedComponentIn Gᶜ A.source ⊆ π ⁻¹' V := by
      intro x hx
      change π x ∈ V
      rw [hc A.source x hx]
      exact hpV
    obtain ⟨n, hn⟩ := (A.matching.eventually_source_cap_subset (hV.preimage hπ) hsub).exists
    have hpCap : p ∈ ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (A.matching.address n)) := by
      have ht := A.matching.nested n
        (mem_iInter.mp (A.matching.target ▸ mem_connectedComponentIn A.matching.outside) (n + 1))
      exact (congrArg (fun t : Sphere => t ∈ ((↑) : ℂ → Sphere) ''
        jordanInterior (L.contours n (A.matching.address n))) A.point_eq).mp ht
    have hOpen := OnePoint.isOpen_image_coe.mpr
      (jordanInterior_isOpen (L.contours n (A.matching.address n)))
    filter_upwards [hOpen.mem_nhds hpCap] with z hz
    obtain ⟨x, hx, hproj⟩ := A.matching.projection_in_source_cap hG π n hz
    change L.sourceProjection hG π z ∈ V
    rw [hproj]
    exact hn hx

end AssignedRealModelLimit
end CircleDomainRigidity.FiniteTransfer

end

end OAI

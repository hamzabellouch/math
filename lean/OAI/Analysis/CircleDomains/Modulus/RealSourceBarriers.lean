import OAI.Analysis.CircleDomains.Transfer.RealTargetEnds
import OAI.Analysis.CircleDomains.Transfer.ShrinkingRealModels

namespace OAI

/-! Local plateaus of the original quotient tests collapse their corresponding full ends. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem source_cap_antitone :
    Antitone (fun n => closedTerminalCap ((L.cores n).disk (E.address n))) := by
  apply antitone_nat_of_succ_le
  intro n
  have hs := (matched_jordan_disk_subset_iff L.conformal.bijOn.injOn
    ((L.cores n).disk (E.address n)) ((L.cores (n + 1)).disk (E.address (n + 1)))
    (L.contours n (E.address n)) (L.contours (n + 1) (E.address (n + 1)))
    ((L.cores (n + 1)).boundary_subset_domain (E.address (n + 1)))
    (L.boundary (n + 1) (E.address (n + 1))) (L.side n (E.address n))).mpr (E.nested n)
  exact hs.trans (image_mono subset_closure)

theorem exists_positive_level_in_neighborhood
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U) :
    ∃ n, 0 < n ∧ closedTerminalCap ((L.cores n).disk (E.address n)) ⊆ π ⁻¹' U := by
  have hsub : (⋂ n, closedTerminalCap ((L.cores n).disk (E.address n))) ⊆ π ⁻¹' U := by
    rw [← E.source]
    intro x hx
    have he := (hr q x).mpr (Or.inr ⟨hq, hx⟩)
    change π x ∈ U
    rw [← he]
    exact hqU
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.source_cap_antitone
    (hU.preimage hπ) hsub
  exact ⟨n + 1, Nat.succ_pos _, (E.source_cap_antitone (Nat.le_succ n)).trans hn⟩

theorem exists_positive_level_test_one
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (l : ℕ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (hone : ∀ x ∈ U ∩ d.source, d.coordinate l x = 1) :
    ∃ n, 0 < n ∧ ∀ z ∈ frontier (jordanInterior ((L.cores n).disk (E.address n))),
      d.physical l (Complex.equivRealProdCLM z) = 1 := by
  obtain ⟨n, hn, hcap⟩ := E.exists_positive_level_in_neighborhood hπ hr hq hU hqU
  refine ⟨n, hn, ?_⟩
  intro z hz
  have hzG := (L.cores n).boundary_subset_domain (E.address n) ⟨z, hz, rfl⟩
  rw [d.pullback l z hzG]
  exact hone (π z) ⟨hcap ⟨z, frontier_subset_closure hz, rfl⟩, d.source_map z hzG⟩

theorem target_eq_singleton_of_plane_subsingleton (h : E.plane.Subsingleton) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  apply Subset.antisymm
  · intro p hp
    have hpoint : E.point ∈ ((↑) : ℂ → Sphere) '' E.plane :=
      E.sphere_image_plane.symm ▸ mem_connectedComponentIn E.outside
    rw [← E.sphere_image_plane] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨w, hw, he⟩ := hpoint
    exact (congrArg ((↑) : ℂ → Sphere) (h hz hw)).trans he
  · exact singleton_subset_iff.mpr (mem_connectedComponentIn E.outside)

theorem target_eq_singleton_of_small_local_plateaus
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ (l : ℕ) (U : Set Sphere),
      IsOpen U ∧ π q ∈ U ∧ (∀ x ∈ U ∩ d.source, d.coordinate l x = 1) ∧
      (∀ z ∈ frontier (jordanInterior ((L.cores 0).disk (E.address 0))),
        d.physical l (Complex.equivRealProdCLM z) = 0) ∧
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) < δ) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  choose labels U hU hqU hOne hZero hsize using fun k => hsmall (modelError k) (modelError_pos k)
  choose levels hlevels hvalues using fun k =>
    E.exists_positive_level_test_one hπ hr hq (labels k) (hU k) (hqU k) (hOne k)
  apply E.target_eq_singleton_of_plane_subsingleton
  apply E.subsingleton_of_small_tests hsard hsch harea hG hε
    levels labels hlevels hvalues hZero
  exact squeeze_zero (fun k => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (fun k => (hsize k).le) modelError_tendsto

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI

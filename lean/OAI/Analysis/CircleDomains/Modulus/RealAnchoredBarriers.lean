import OAI.Analysis.CircleDomains.Modulus.RealSourceBarriers

namespace OAI

/-! Collapse with a fixed outer zero contour, as used by the selected barriers. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

theorem exists_positive_level_in_source_open
    {W : Set Sphere} (hW : IsOpen W) (hCW : connectedComponentIn Gᶜ q ⊆ W) :
    ∃ n, 0 < n ∧ closedTerminalCap ((L.cores n).disk (E.address n)) ⊆ W := by
  obtain ⟨n, hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap _).isClosed) E.source_cap_antitone hW
    (E.source ▸ hCW)
  exact ⟨n + 1, Nat.succ_pos _, (E.source_cap_antitone (Nat.le_succ n)).trans hn⟩

/-- The source outer contour is fixed independently of the shrinking tests.
Its target contour and the common radius bound are constructed once. -/
theorem target_eq_singleton_of_small_anchored_plateaus
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (A : SmoothJordanCore G) (j : Fin A.count)
    (hCA : connectedComponentIn Gᶜ q ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ (l : ℕ) (U : Set Sphere),
      IsOpen U ∧ π q ∈ U ∧ (∀ x ∈ U ∩ d.source, d.coordinate l x = 1) ∧
      (∀ z ∈ frontier (jordanInterior (A.disk j)),
        d.physical l (Complex.equivRealProdCLM z) = 0) ∧
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) < δ) :
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point = {E.point} := by
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  obtain ⟨J, _, _, hJ, hJs⟩ := exists_matched_image_core hsch hG hconn hinf
    L.conformal.1 L.conformal.bijOn.injOn (by simp) A
  choose labels U hU hqU hOne hZero hsize using fun k => hsmall (modelError k) (modelError_pos k)
  have hlevels (k : ℕ) : ∃ n, 0 < n ∧
      closedTerminalCap ((L.cores n).disk (E.address n)) ⊆
        (π ⁻¹' U k) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) := by
    apply E.exists_positive_level_in_source_open
      ((hU k).preimage hπ |>.inter (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen _)))
    intro x hx
    refine ⟨?_, hCA hx⟩
    change π x ∈ U k
    rw [← (hr q x).mpr (Or.inr ⟨hq, hx⟩)]
    exact hqU k
  choose levels hpos hcap using hlevels
  have hone (k : ℕ) : ∀ z ∈ frontier (jordanInterior ((L.cores (levels k)).disk (E.address (levels k)))),
      d.physical (labels k) (Complex.equivRealProdCLM z) = 1 := by
    intro z hz
    have hzG := (L.cores (levels k)).boundary_subset_domain (E.address (levels k)) ⟨z, hz, rfl⟩
    rw [d.pullback _ z hzG]
    exact hOne k (π z) ⟨(hcap k ⟨z, frontier_subset_closure hz, rfl⟩).1, d.source_map z hzG⟩
  have hnested (k : ℕ) : closure (jordanInterior (L.contours (levels k) (E.address (levels k)))) ⊆
      jordanInterior (J j) := by
    have ht := (matched_jordan_disk_subset_iff L.conformal.bijOn.injOn
      (A.disk j) ((L.cores (levels k)).disk (E.address (levels k)))
      (J j) (L.contours (levels k) (E.address (levels k)))
      ((L.cores (levels k)).boundary_subset_domain (E.address (levels k)))
      (L.boundary (levels k) (E.address (levels k))) (hJs j)).mp
        ((hcap k).trans inter_subset_right)
    intro z hz
    exact OnePoint.coe_injective.mem_set_image.mp (ht ⟨z, hz, rfl⟩)
  let B (k : ℕ) : RetainedRealBarrier d L.function (labels k) := {
    inner := L.cores (levels k), outer := A,
    inner_index := E.address (levels k), outer_index := j,
    value_one := hone k, value_zero := hZero k,
    target_inner := L.contours (levels k) (E.address (levels k)), target_outer := J j,
    inner_image := L.boundary (levels k) (E.address (levels k)), outer_image := hJ j,
    inner_side := L.side (levels k) (E.address (levels k)), outer_side := hJs j,
    nested := hnested k }
  obtain ⟨R, _, hR⟩ := (isCompact_closure_jordanInterior (J j)).isBounded.exists_pos_norm_lt
  have hF : ContinuousOn L.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (L.conformal.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  apply E.target_eq_singleton_of_plane_subsingleton
  apply M.subsingleton_of_vanishing_barriers (L := max (3 * M.radius) R)
    hsard hsch harea hG hε L.subsequence L.strict.tendsto_atTop
    L.function hF L.converges labels B E.plane_compact E.plane_connected
    (fun k => E.plane_inside (levels k)) (le_max_left _ _) ?_ ?_
  · intro k z hz
    rw [mem_ball, dist_zero_right]
    exact (hR z hz).trans_le (le_max_right _ _)
  · exact squeeze_zero (fun k => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (fun k => (hsize k).le) modelError_tendsto

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI

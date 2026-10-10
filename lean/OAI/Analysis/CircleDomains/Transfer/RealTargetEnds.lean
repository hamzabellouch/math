import OAI.Analysis.CircleDomains.Transfer.RealMarkedModels
import OAI.Analysis.CircleDomains.Modulus.RealBarrierCollapse

namespace OAI

/-! Full corresponding target ends and their collapse by actual source tests. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure RealTargetEnd {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} {M : RealModelExhaustion d O ε}
    (L : AssignedRealModelLimit M) (q : Sphere) where
  address : ∀ n, Fin (L.cores n).count
  point : Sphere
  outside : point ∈ (extendAtInfinity L.function '' G)ᶜ
  source : connectedComponentIn Gᶜ q = ⋂ n, closedTerminalCap ((L.cores n).disk (address n))
  target : connectedComponentIn (extendAtInfinity L.function '' G)ᶜ point =
    ⋂ n, closedTerminalCap (L.contours n (address n))
  nested : ∀ n, closedTerminalCap (L.contours (n + 1) (address (n + 1))) ⊆
    ((↑) : ℂ → Sphere) '' jordanInterior (L.contours n (address n))

theorem AssignedRealModelLimit.exists_target_end
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    {M : RealModelExhaustion d O ε} (L : AssignedRealModelLimit M)
    (hG : IsOpen G) {q : Sphere} (hq : q ∈ Gᶜ) : Nonempty (RealTargetEnd L q) := by
  obtain ⟨b, p, hp, hs, ht, hn⟩ := corresponding_target_end_of_source hG
    L.conformal.1 L.conformal.bijOn.injOn L.cores L.contours L.nested L.exhausts
    L.disjoint L.image_core L.boundary L.side hq
  exact ⟨⟨b, p, hp, hs, ht, hn⟩⟩

namespace RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {L : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd L q)

def plane : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹'
  connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point

theorem cap_antitone : Antitone (fun n => closedTerminalCap (L.contours n (E.address n))) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (E.nested n).trans (image_mono subset_closure)

theorem plane_inside (n : ℕ) : E.plane ⊆ jordanInterior (L.contours n (E.address n)) := by
  intro z hz
  have hc : (z : Sphere) ∈ ⋂ j, closedTerminalCap (L.contours j (E.address j)) := E.target ▸ hz
  exact OnePoint.coe_injective.mem_set_image.mp
    (E.nested n (mem_iInter.mp hc (n + 1)))

theorem cap_inside_outer {n : ℕ} (hn : 0 < n) :
    closure (jordanInterior (L.contours n (E.address n))) ⊆
      jordanInterior (L.contours 0 (E.address 0)) := by
  intro z hz
  have hc : (z : Sphere) ∈ closedTerminalCap (L.contours 1 (E.address 1)) :=
    E.cap_antitone hn ⟨z, hz, rfl⟩
  exact OnePoint.coe_injective.mem_set_image.mp (E.nested 0 hc)

theorem infinity_not_mem : OnePoint.infty ∉
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  intro h
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  apply connectedComponentIn_subset _ _ h
  exact ⟨OnePoint.infty, hinf, by simp⟩

theorem sphere_image_plane : ((↑) : ℂ → Sphere) '' E.plane =
    connectedComponentIn (extendAtInfinity L.function '' G)ᶜ E.point := by
  apply image_preimage_eq_of_subset
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (E.infinity_not_mem hp).elim
  | coe z => exact ⟨z, rfl⟩

theorem plane_compact : IsCompact E.plane := by
  apply isCompact_finite_preimage _ E.infinity_not_mem
  rw [E.target]
  exact isClosed_iInter fun n => (isCompact_closedTerminalCap _).isClosed

theorem plane_connected : IsConnected E.plane := by
  have hc : IsConnected (((↑) : ℂ → Sphere) '' E.plane) := by
    rw [E.sphere_image_plane]
    exact isConnected_connectedComponentIn_iff.mpr E.outside
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hc.isPreconnected⟩
  obtain ⟨p, z, hz, _⟩ := hc.nonempty
  exact ⟨z, hz⟩

def barrier {n : ℕ} (hn : 0 < n) (l : ℕ)
    (hOne : ∀ z ∈ frontier (jordanInterior ((L.cores n).disk (E.address n))),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (hZero : ∀ z ∈ frontier (jordanInterior ((L.cores 0).disk (E.address 0))),
      d.physical l (Complex.equivRealProdCLM z) = 0) : RetainedRealBarrier d L.function l where
  inner := L.cores n
  outer := L.cores 0
  inner_index := E.address n
  outer_index := E.address 0
  value_one := hOne
  value_zero := hZero
  target_inner := L.contours n (E.address n)
  target_outer := L.contours 0 (E.address 0)
  inner_image := L.boundary n (E.address n)
  outer_image := L.boundary 0 (E.address 0)
  inner_side := L.side n (E.address n)
  outer_side := L.side 0 (E.address 0)
  nested := E.cap_inside_outer hn

theorem subsingleton_of_small_tests
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (levels labels : ℕ → ℕ) (hlevels : ∀ k, 0 < levels k)
    (hOne : ∀ k, ∀ z ∈ frontier (jordanInterior ((L.cores (levels k)).disk (E.address (levels k)))),
      d.physical (labels k) (Complex.equivRealProdCLM z) = 1)
    (hZero : ∀ k, ∀ z ∈ frontier (jordanInterior ((L.cores 0).disk (E.address 0))),
      d.physical (labels k) (Complex.equivRealProdCLM z) = 0)
    (hsmall : Tendsto (fun k =>
      Real.sqrt (∫ x in realChartDomain G,
        gradientEnergy (d.physical (labels k)) (fun z => sphericalMetricFactor z • 1) x) +
      Real.sqrt (∑' s, (d.upper (labels k) s - d.lower (labels k) s) ^ 2)) atTop (𝓝 0)) :
    E.plane.Subsingleton := by
  have hF : ContinuousOn L.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (L.conformal.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  obtain ⟨R, _, hR⟩ := (isCompact_closure_jordanInterior
    (L.contours 0 (E.address 0))).isBounded.exists_pos_norm_lt
  let D := max (3 * M.radius) R
  apply M.subsingleton_of_vanishing_barriers (L := D) hsard hsch harea hG hε
    L.subsequence L.strict.tendsto_atTop L.function hF L.converges labels
    (fun k => E.barrier (hlevels k) (labels k) (hOne k) (hZero k))
    E.plane_compact E.plane_connected (fun k => E.plane_inside (levels k)) (le_max_left _ _) ?_ hsmall
  intro k z hz
  have h := hR z hz
  exact mem_ball_zero_iff.mpr (h.trans_le (le_max_right _ _))

end RealTargetEnd

end CircleDomainRigidity.FiniteTransfer

end

end OAI

import OAI.Analysis.CircleDomains.Selection.FixedRealExclusion
import OAI.Analysis.CircleDomains.Modulus.ProtrusionBarrierObstruction

namespace OAI

/-! Small real barriers at an actual protruding end exclude a whole open neighborhood.
The retained contour is selected from the original end before testing any later model. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

namespace RealTargetEnd
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

 theorem exists_core_in_neighborhood_avoiding_anchor
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    {K : Set ℂ} (hK : IsCompact K)
    (hKA : ((↑) : ℂ → Sphere) '' K ⊆ extendAtInfinity A.function '' G) :
    ∃ k : ℕ, closedTerminalCap ((A.cores k).disk (E.address k)) ⊆ π ⁻¹' U ∧
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
  refine ⟨k, (E.source_cap_antitone (le_max_left n m)).trans hsource, ?_⟩
  apply Set.disjoint_left.mpr
  intro z hzK hzcap
  exact (E.cap_antitone (le_max_right n m)).trans htargetm
    ⟨z, hzcap, rfl⟩ (mem_image_of_mem _ hzK)

end RealTargetEnd

namespace LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 theorem exists_open_real_barrier_exclusion
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hconn : IsConnected G) (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (u : (ℝ × ℝ) → ℝ)
    (hone : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U →
      u (Complex.equivRealProdCLM z) = 1)
    (hzero : ∀ z ∈ closure (jordanInterior T.sourceAnchor),
      u (Complex.equivRealProdCLM z) = 0)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) (closedBall T.center T.radius))
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
      gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β < T.barrierThreshold) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧
      finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ V ∧
      ∀ {S' : Type*} {π' : Sphere → Sphere} {σ' : S' → Sphere}
        {d' : CountableRealCoordinates G π' σ'} {O' : ℕ → S' → Set Sphere} {ε' : ℕ → ℝ}
        (M' : RealModelExhaustion d' O' ε') (A' : AssignedRealModelLimit M') (l : ℕ),
        Tendsto ε' atTop (𝓝 0) → 3 * M'.radius ≤ T.boundRadius →
        d'.physical l = u → Real.sqrt (∑' s, (d'.upper l s - d'.lower l s) ^ 2) ≤ β →
        finiteSourceMap A'.function (A'.plane_open_embedding hG).1 ∉ V := by
  have hKA : ((↑) : ℂ → Sphere) '' closedBall T.anchorCenter T.anchorRadius ⊆
      extendAtInfinity A.function '' G := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hp, he⟩ := T.anchor_image hz
    exact ⟨p, T.source_inside (subset_closure hp), by simp only [extendAtInfinity_coe, he]⟩
  obtain ⟨k, hcap, hdisj⟩ := E.exists_core_in_neighborhood_avoiding_anchor
    hπ hr hq hU hqU (isCompact_closedBall _ _) hKA
  have hone' : ∀ z ∈ frontier (jordanInterior ((A.cores k).disk (E.address k))),
      u (Complex.equivRealProdCLM z) = 1 := by
    intro z hz
    exact hone z ((A.cores k).boundary_subset_domain (E.address k) ⟨z, hz, rfl⟩)
      (hcap ⟨z, frontier_subset_closure hz, rfl⟩)
  have hA := A.plane_open_embedding hG
  obtain ⟨V, hV, hmem, hexclude⟩ := exists_open_fixed_core_real_exclusion hsch harea hG hconn
    (A.cores k) (E.address k) A.function hA.1 hA.2.1 hA.2.2
    (A.contours k (E.address k)) (A.boundary k (E.address k)) (A.side k (E.address k))
    T.sourceAnchor T.source_inside T.anchorCenter T.anchorRadius T.anchor_image hdisj
    T.compact (T.in_component.trans (E.plane_inside k)) isClosed_closedBall
    (convex_closedBall T.center T.radius) T.in_region T.anchor_region hP hPG hPW
    T.direction measurableSet_Icc T.projection T.boundRadius T.region_bound
  refine ⟨V, hV, hmem, ?_⟩
  intro S' π' σ' d' O' ε' M' A' l hε' hR heq hband
  apply hexclude M' A' l hε' hR
    (by simpa only [heq] using hone') (by simpa only [heq] using hzero)
  rw [heq]
  have hRpos : 0 < T.boundRadius :=
    lt_of_lt_of_le (mul_pos (by norm_num) M.radius_pos) T.model_bound
  have hden : 0 < (Real.sqrt Real.pi + 2) * T.boundRadius := by positivity
  have hstrict : ((Real.sqrt Real.pi + 2) * T.boundRadius) *
      (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β) < T.upper - T.lower := by
    have h := (lt_div_iff₀ hden).mp hsmall
    simpa only [mul_comm] using h
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr T.width_pos.le)]
  calc
    _ ≤ Real.sqrt Real.pi * T.boundRadius * Real.sqrt
          (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) +
        2 * T.boundRadius * β := by gcongr
    _ ≤ ((Real.sqrt Real.pi + 2) * T.boundRadius) *
        (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
          gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β) := by
      nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg Real.pi) hRpos.le) hβ,
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRpos.le)
          (Real.sqrt_nonneg (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy u (fun z => sphericalMetricFactor z • 1) x))]
    _ < T.upper - T.lower := hstrict

end LocalEndTestGeometry
end CircleDomainRigidity.FiniteTransfer

end

end OAI

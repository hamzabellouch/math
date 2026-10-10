import OAI.Analysis.CircleDomains.Selection.LocalFixedRealExclusion

namespace OAI

/-! A strictly larger comparison radius gives an open radius interval in
the countable selection space while retaining the same real barrier test. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)

 def selectionRadius : ℝ := T.boundRadius + 1

 theorem model_lt_selectionRadius : 3 * M.radius < T.selectionRadius := by
  have h := T.model_bound
  dsimp [selectionRadius]
  linarith

 def selectionThreshold : ℝ := (T.upper - T.lower) /
   ((Real.sqrt Real.pi + 2) * T.selectionRadius)

 theorem selectionThreshold_pos : 0 < T.selectionThreshold := by
  apply div_pos (sub_pos.mpr T.width_pos)
  apply mul_pos (by positivity)
  exact (mul_pos (by norm_num) M.radius_pos).trans T.model_lt_selectionRadius

 theorem exists_open_real_barrier_exclusion_at_radius
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
    (R : ℝ) (hTR : T.boundRadius ≤ R)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
      gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β < (T.upper - T.lower) / ((Real.sqrt Real.pi + 2) * R)) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧
      finiteSourceMap A.function (A.plane_open_embedding hG).1 ∈ V ∧
      ∀ {S' : Type*} {π' : Sphere → Sphere} {σ' : S' → Sphere}
        {d' : CountableRealCoordinates G π' σ'} {O' : ℕ → S' → Set Sphere} {ε' : ℕ → ℝ}
        (M' : RealModelExhaustion d' O' ε') (A' : AssignedRealModelLimit M') (l : ℕ),
        Tendsto ε' atTop (𝓝 0) → 3 * M'.radius ≤ R →
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
    T.direction measurableSet_Icc T.projection R
      (T.region_bound.trans (closedBall_subset_closedBall hTR))
  refine ⟨V, hV, hmem, ?_⟩
  intro S' π' σ' d' O' ε' M' A' l hε' hR heq hband
  apply hexclude M' A' l hε' hR
    (by simpa only [heq] using hone') (by simpa only [heq] using hzero)
  rw [heq]
  have hRpos : 0 < R :=
    lt_of_lt_of_le (mul_pos (by norm_num) M.radius_pos) (T.model_bound.trans hTR)
  have hden : 0 < (Real.sqrt Real.pi + 2) * R := by positivity
  have hstrict : ((Real.sqrt Real.pi + 2) * R) *
      (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β) < T.upper - T.lower := by
    have h := (lt_div_iff₀ hden).mp hsmall
    simpa only [mul_comm] using h
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr T.width_pos.le)]
  calc
    _ ≤ Real.sqrt Real.pi * R * Real.sqrt
          (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) +
        2 * R * β := by gcongr
    _ ≤ ((Real.sqrt Real.pi + 2) * R) *
        (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
          gradientEnergy u (fun z => sphericalMetricFactor z • 1) x) + β) := by
      nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg Real.pi) hRpos.le) hβ,
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRpos.le)
          (Real.sqrt_nonneg (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy u (fun z => sphericalMetricFactor z • 1) x))]
    _ < T.upper - T.lower := hstrict

end CircleDomainRigidity.FiniteTransfer.LocalEndTestGeometry

end

end OAI

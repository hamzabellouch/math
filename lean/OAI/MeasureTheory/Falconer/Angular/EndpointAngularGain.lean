import OAI.MeasureTheory.Falconer.Estimates.EndpointOrientedGain
import OAI.MeasureTheory.Falconer.Geometry.EndpointChartRadius

namespace OAI

/-! # Uniform endpoint angular gain in every ambient dimension h+3 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem endpoint_dyadic_angular_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρsmall,hstable⟩ := exists_endpoint_chart_radius h
  obtain ⟨ε,c₁,hε,hc₁,N₁,hgain⟩ := endpoint_oriented_chart_gain hLW ht ht' hζ hC hρ hρsmall hstable
  let H : ℝ := (2/ρ+1)^(h+3)
  let c : ℝ := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := dyadic_inverse_tendsto.eventually
    (eventually_const_mul_rpow_lt (show c < c₁ by dsimp [c]; linarith) H)
  obtain ⟨N₂,habs⟩ := eventually_atTop.mp habs
  refine ⟨ε,c,hε,hc,N₁+N₂,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hH : H*δ^c₁ ≤ δ^c := (habs N (by omega)).2.le
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ)) :=
    (Measure.restrict_le_self _).trans (hνball w j hj)
  have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
      ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
        ENNReal.ofReal (δ^(-ε)*r^ζ) :=
    (Measure.restrict_le_self _).trans (hslab w r hr hr1)
  have hg := hgain N (by omega) ι μ ν' w₀ E J v hνsupport hμ hμmass hν'mass
    hμball hν'ball hslab' hE hJ hJN hEb hanchors hcover
  exact (not_lt_of_ge hg) hw₀

end Falconer

end OAI

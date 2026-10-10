import OAI.MeasureTheory.Falconer.Geometry.NonendpointChartGain
import OAI.MeasureTheory.Falconer.Slicing.SmallGaussianChart

namespace OAI

/-! # The nonendpoint angular gain in every ambient dimension h+2 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_dyadic_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρhalf,hstable,hchart⟩ := exists_small_gaussian_chart_radius h
  obtain ⟨ε,c₁,δ₁,hε,hc₁,hδ₁,hgain⟩ := nonendpoint_chart_angular_gain hpublished hq hq' hqt ht
    hC hρ hρhalf hstable hchart
  let H : ℝ := (2/ρ+1)^(h+2)
  let c := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(c₁-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop H)
  obtain ⟨δ₂,hδ₂,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp habs
  refine ⟨ε,c,min δ₁ δ₂,hε,hc,lt_min hδ₁ hδ₂,?_⟩
  intro N κ _ _ μ ν _ _ E J a hδsmall hμ hμmass hνmass hμball hνball hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hH : H*δ^c₁ ≤ δ^c := by
    have ha : H ≤ δ^(-(c₁-c)) := hready ⟨hδ,hδsmall.trans_le (min_le_right _ _)⟩
    have hh := rpow_absorb_constant (t := -c₁) (u := -c) hδ (by
      convert ha using 1; ring_nf)
    simpa only [neg_neg] using hh
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (x : Sphere (h+2)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^q) :=
    (Measure.restrict_le_self _).trans (hνball x j hj)
  have hg := hgain N κ μ ν' w₀ E J a (hδsmall.trans_le (min_le_left _ _))
    hνsupport hμ hμmass hν'mass hμball hν'ball hE hJ hJN hEb hanchors hcover
  have hgle : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₁) := by
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
      ENNReal.ofReal_le_ofReal hg
  exact (not_lt_of_ge hgle) hw₀

end Falconer

end OAI

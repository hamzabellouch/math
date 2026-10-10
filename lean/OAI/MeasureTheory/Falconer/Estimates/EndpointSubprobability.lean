import OAI.MeasureTheory.Falconer.Geometry.EndpointChartGain
import OAI.MeasureTheory.Falconer.Geometry.EndpointNormalize

namespace OAI

/-! # Endpoint small-cap gain for original subprobability direction laws -/

namespace Falconer
open Set MeasureTheory Real
open scoped ENNReal

theorem endpoint_chart_subprobability_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ ρ) →
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
  obtain ⟨ε₀,c₀,hε₀,hc₀,N₀,hgain⟩ := endpoint_chart_angular_gain hLW ht ht' hζ hC hρ hρsmall hstable
  let ε := ε₀/2
  let c := min ε c₀
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := lt_min hε hc₀
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hν hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hpow {p q : ℝ} (hpq : p ≤ q) : δ^q ≤ δ^p :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hpq
  by_cases hmass : ν univ ≤ ENNReal.ofReal (δ^ε)
  · calc
      (μ.prod ν) E ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = μ univ*ν univ := by rw [← univ_prod_univ,Measure.prod_prod]
      _ ≤ 1*ENNReal.ofReal (δ^ε) := mul_le_mul' hμmass hmass
      _ ≤ ENNReal.ofReal (δ^c) := by
        rw [one_mul]
        exact ENNReal.ofReal_le_ofReal (hpow (min_le_left _ _))
  · have hmass' : ENNReal.ofReal (δ^ε) ≤ ν univ := (lt_of_not_ge hmass).le
    have hν0 : ν univ ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ ε)).trans_le hmass')
    let ν' : Measure (Sphere (h+3)) := normalizedSliceLaw ν hν0
    have hnorm (S : Set (Sphere (h+3))) (r q : ℝ) (hr : 0 ≤ r)
        (hS : ν S ≤ ENNReal.ofReal (δ^(-ε)*r^q)) :
        ν' S ≤ ENNReal.ofReal (δ^(-ε₀)*r^q) := by
      have hh := normalizedSliceLaw_power_bound ν hν0 hδ hr hmass' S hS
      have he : -ε-ε = -ε₀ := by dsimp [ε]; ring
      simpa only [he] using hh
    have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
        ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε₀)*(1/(2:ℝ)^j)^(h+1:ℝ)) :=
      hnorm _ _ _ (by positivity) (hνball w j hj)
    have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
        ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal (δ^(-ε₀)*r^ζ) :=
      hnorm _ r ζ (hδ.le.trans hr) (hslab w r hr hr1)
    have hL : δ^(-ε) ≤ δ^(-ε₀) := hpow (neg_le_neg hεle)
    have hg := hgain N hN ι μ ν' E J v (normalizedSliceLaw_ae ν hν0 hν) hμ hμmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL
          (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      hν'ball hslab' hE hJ
      (fun w => (hJN w).trans (hpow (by linarith : -(h+1:ℝ)-ε₀ ≤ -(h+1:ℝ)-ε)))
      hEb hanchors hcover
    have hg' : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₀) := by
      simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
        ENNReal.ofReal_le_ofReal hg
    exact (incidence_le_normalized_direction μ ν hν0 hνmass E).trans
      (hg'.trans (ENNReal.ofReal_le_ofReal (hpow (min_le_right _ _))))

end Falconer

end OAI

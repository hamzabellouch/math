import OAI.Geometry.RCD.Harmonic.RadialVariationBound

namespace OAI

/-! # First variation for a family of radial contractions

The family may use a different optimal plan at each contraction scale.
Uniform compression and shrinking length suffice for the signed limit.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem radial_first_variation_eventually_gt
    (π : ℕ → Measure C(Time, X)) [∀ k, IsProbabilityMeasure (π k)]
    (hg : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ k, ∀ t : Time, (π k).map (fun γ => γ t) ≤ C • μ)
    (hD : ∀ k, MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 (π k))
    (ν : Measure X) (hinit : ∀ k, (π k).map (fun γ => γ 0) = ν)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R)
    (hlen : ∀ k, ∀ᵐ γ ∂π k, dist (γ 0) (γ 1) ≤ a k * R)
    (q g : SobolevSpace μ hQ)
    (hcost : ∀ k, (∫ γ, dist (γ 0) (γ 1) ^ 2 ∂π k) =
      a k ^ 2 * weightedGradientSquare μ hQ ν q)
    (hdec : ∀ k, (∫ γ, SobolevSpace.toLp μ hQ q (γ 0) -
      SobolevSpace.toLp μ hQ q (γ 1) ∂π k) =
      (a k - a k ^ 2 / 2) * weightedGradientSquare μ hQ ν q)
    {c : ℝ} (hcq : c < -weightedGradientPair μ hQ ν q g) :
    ∀ᶠ k in atTop, c <
      (∫ γ, SobolevSpace.toLp μ hQ g (γ 1) - SobolevSpace.toLp μ hQ g (γ 0) ∂π k) / a k := by
  let : IsProbabilityMeasure ν := (hinit 0) ▸ inferInstance
  have hν : ν ≤ C • μ := (hinit 0) ▸ hc 0 0
  let A := weightedGradientSquare μ hQ ν q
  let b := -weightedGradientPair μ hQ ν q g
  let δ := (b - c) / 4
  have hδ : 0 < δ := by dsimp [δ, b]; linarith
  have hsec := weightedGradientPair_secant_limit μ hQ hC hν q g
  have hcδ : c + 3 * δ < b := by dsimp [δ]; linarith
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ c + 3 * δ <
      (A - weightedGradientSquare μ hQ ν (q + ε • g)) / (2 * ε) := by
    filter_upwards [self_mem_nhdsWithin, hsec.eventually (Ioi_mem_nhds hcδ)] with ε h0 hb
    exact ⟨h0, hb⟩
  obtain ⟨ε, hε, hεbound⟩ := hev.exists
  let η := ε * δ / (R + 1)
  have hη : 0 < η := div_pos (mul_pos hε hδ) (by positivity)
  obtain ⟨d, hd, hshort⟩ := uniform_short_plan_pullback μ
    (SobolevSpace.minimalSlope μ hQ (q + ε • g)) hC hη
  have hsmall : ∀ᶠ k in atTop, a k * R < d := by
    have hh : Tendsto (fun k => a k * R) atTop (𝓝 0) := by
      simpa only [zero_mul] using ha0.mul_const R
    exact hh.eventually (Iio_mem_nhds hd)
  let E := weightedGradientSquare μ hQ ν (q + ε • g)
  have hηeq : (R + 1) * η = ε * δ := by
    dsimp only [η]
    field_simp
  have htarget : c < ((A - E) / 2 - R * η) / ε := by
    apply (lt_div_iff₀ hε).mpr
    have hh := (lt_div_iff₀ (show 0 < 2 * ε by positivity)).mp hεbound
    nlinarith
  have hlim : Tendsto (fun k => ((1 - a k / 2) * A - (A + E) / 2 - R * η) / ε)
      atTop (𝓝 (((A - E) / 2 - R * η) / ε)) := by
    have hh : Continuous (fun t : ℝ => ((1 - t / 2) * A - (A + E) / 2 - R * η) / ε) := by
      fun_prop
    have hh0 := (hh.continuousAt (x := 0)).tendsto.comp ha0
    change Tendsto (fun k => ((1 - a k / 2) * A - (A + E) / 2 - R * η) / ε)
      atTop (𝓝 (((1 - 0 / 2) * A - (A + E) / 2 - R * η) / ε)) at hh0
    convert hh0 using 1
    congr 1
    ring
  filter_upwards [hsmall, hlim.eventually (Ioi_mem_nhds htarget)] with k hk hlower
  have hclose := hshort (π k) (hg k) (hc k) (hD k)
    ((hlen k).mono fun _ hγ => hγ.trans hk.le)
  have hbound := radial_variation_lower_bound μ hQ (π k) (hg k) hC (hc k) (hD k)
    q g (ha k) hR hε hη.le (hlen k) (hcost k) (hdec k) (fun t => (hclose t).le)
  rw [hinit k] at hbound
  exact hlower.trans_le hbound

end RegularPointCoordinates

end OAI

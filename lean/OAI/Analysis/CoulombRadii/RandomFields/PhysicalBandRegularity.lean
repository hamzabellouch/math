import Mathlib
import OAI.Analysis.CoulombRadii.Packets.BandOscillation
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorCount
import OAI.Analysis.CoulombRadii.Packets.PacketBandGeometry

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_posterior_band_bounds (g : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g z=0) :
    ∃ B D : ℝ,0 ≤ B ∧ 0 ≤ D ∧
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν],
    ∀ {c r₀ s r L : ℝ},0 < c → 0 < r₀ → 0 < s → 0 < r → 1 ≤ L → r₀ ≤ r → r ≤ s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
    ∀ (rads : Fin J → ℝ),(∀ k,0 ≤ rads k) → ∀ {j : ℕ} (k : Fin J),j ≤ k.val →
    Real.sqrt 3*(rads k)^(101/100:ℝ) ≤ r/12 →
    ∀ᵐ sample ∂observationLaw J ν,
      let μ := conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation rads j)
        g c r₀ s (tailObservation rads j sample)
      let m := rawCount {x : Position | r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*r} (observedOrdered rads k sample)
      let τ := c*(r/3)*(r/3)^packetExponent
      (∀ y : Position,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → μ y ≤ (B/τ^3)*m) ∧
      (∀ y z : Position,r/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*r → r/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*r →
        |μ y-μ z| ≤ (D/τ^4)*‖y-z‖*m) := by
  obtain ⟨B,D,hB,hD,hbound,hlip⟩ := schwartz_square_bounded_lipschitz g
  refine ⟨B,D,hB,hD,?_⟩
  intro n J ν hν c r₀ s r L hc hr₀ hs hr hL hrr₀ hrs hscale hwidth rads hrads j k hk hnoise
  let S := {x : Position | r/3 ≤ ‖x‖ ∧ ‖x‖ ≤ 10*L*r}
  let T := {x : Position | r/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 8*L*r}
  let O := {x : Position | r/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*r}
  have hS : MeasurableSet S := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hO : MeasurableSet O := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgs : HasCompactSupport (g : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hpost := posterior_count_le_observed ν rads hrads k hk hS hO
    (fun x hx y hxy => packet_band_observation_support hr hL hnoise hx hxy)
  filter_upwards [hpost] with sample hh
  let ν' := ProbabilityTheory.condDistrib Prod.fst (tailObservation rads j) (observationLaw J ν)
    (tailObservation rads j sample)
  have hτ : 0 < c*(r/3)*(r/3)^packetExponent := by positivity
  have H := mixture_packet_band_bounds ν' g.continuous hgs hB hD hbound hlip hc hr₀ hs hτ hS
    (T:=T) (fun y hy x hx => packet_band_center_support hg hc hr₀ hs hr hL hrr₀ hscale hwidth hy.1 hy.2 hx)
    (fun x hx => packet_band_width_lower hc hr₀ hs hr hrs hx.1)
  dsimp only
  constructor
  · intro y hy0 hy1
    exact (H.1 y ⟨hy0,hy1⟩).trans (mul_le_mul_of_nonneg_left hh (by positivity))
  · intro y z hy0 hy1 hz0 hz1
    exact (H.2 y ⟨hy0,hy1⟩ z ⟨hz0,hz1⟩).trans (mul_le_mul_of_nonneg_left hh (by positivity))
end NeutralAtom
end

end

end OAI

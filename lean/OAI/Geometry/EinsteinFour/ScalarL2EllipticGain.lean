import OAI.Geometry.EinsteinFour.ScalarPoissonKernelPotential
import OAI.Geometry.EinsteinFour.ScalarLocalL2Source

namespace OAI

/-! One actual local elliptic gain with merely L2 forcing. The smooth
zeroth-order coefficient is handled as a multiplier of the unknown. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_ball_L2_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u : T) (f : V → ℂ)
    (hf : MemLp f 2 (volume : Measure V))
    (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = ∫ x, ψ x * f x)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    MemSobolev 2 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hc hs
  have houter : MemSobolev 1 2 (M (ψ 1) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ 1) u
      (by simpa only [Nat.cast_one] using hu)
  have hsource : MemSobolev 0 2
      (M (ψ 0) (scalarPerturbedOperator a b u - u - M c u)) :=
    scalar_localize_memSobolev_zero_of_L2_source (ball 0 1) _ f htest
      (ψ 0) (hsupp 0).1 (hsupp 0).2
      ((ψ 0).memLp ∞ (volume : Measure V) |>.mul hf)
  have hgain := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c (ψ 0) (ψ 1) (hnest 0) 0 u (by simpa using houter) (by simpa using hsource)
  simpa only [hψ, zero_add, Nat.cast_ofNat] using hgain

end
end PositiveEinsteinFour.Geometry

end OAI

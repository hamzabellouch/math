import OAI.Geometry.EinsteinFour.ScalarHalfBallCutoffs
import OAI.Geometry.EinsteinFour.ScalarH2EllipticGain

namespace OAI

/-! Local H4 gain where only the smaller-ball forcing is H2. This avoids
assuming any regularity of the forcing outside the coordinate neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_half_ball_H2_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u : T) (hu : MemSobolev 1 2 u)
    (hsource : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev 2 2 (M ψ (scalarPerturbedOperator a b u - u - M c u)))
    (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 4)) :
    MemSobolev 4 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_half_nested_cutoffs (1 / 4)
    (by norm_num) (by norm_num) φ hc hs
  have hF (k : ℕ) := hsource (ψ k) (hsupp k).1 (hsupp k).2
  have houter : MemSobolev 1 2 (M (ψ 3) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ 3) u
      (by simpa only [Nat.cast_one] using hu)
  have hsecond : MemSobolev 2 2 (M (ψ 2) u) := by
    have hg := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
      c (ψ 2) (ψ 3) (hnest 2) 0 u (by simpa using houter)
      ((hF 2).mono (by norm_num))
    simpa using hg
  have hthird : MemSobolev 3 2 (M (ψ 1) u) := by
    have hg := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
      c (ψ 1) (ψ 2) (hnest 1) 1 u (by simpa using hsecond)
      ((hF 1).mono (by norm_num))
    simpa using hg
  have hfinal := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c (ψ 0) (ψ 1) (hnest 0) 2 u (by simpa using hthird) (by simpa using hF 0)
  simpa [hψ] using hfinal

end
end PositiveEinsteinFour.Geometry

end OAI

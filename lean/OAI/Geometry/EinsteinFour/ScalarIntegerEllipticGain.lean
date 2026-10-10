import OAI.Geometry.EinsteinFour.ScalarHalfBallCutoffs
import OAI.Geometry.EinsteinFour.ScalarH2EllipticGain

namespace OAI

/-! The localized integer-order elliptic bootstrap on one fixed half ball. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_half_ball_integer_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (n : ℕ) (c : S) (u : T) (hu : MemSobolev 1 2 u)
    (hsource : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u - u - M c u)))
    (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 4)) :
    MemSobolev ((n : ℝ) + 2) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_half_nested_cutoffs (1 / 4)
    (by norm_num) (by norm_num) φ hc hs
  have hF (k : ℕ) := hsource (ψ k) (hsupp k).1 (hsupp k).2
  have hreg : ∀ k : ℕ, k ≤ n + 1 → ∀ j : ℕ,
      MemSobolev ((k : ℝ) + 1) 2 (M (ψ j) u) := by
    intro k
    induction k with
    | zero =>
      intro _ j
      simpa only [Nat.cast_zero, zero_add, Nat.cast_one] using
        scalar_memSobolev_schwartz_multiplier 1 (ψ j) u (by simpa using hu)
    | succ k ih =>
      intro hk j
      have houter := ih (by omega) (j + 1)
      have hforcing : MemSobolev (k : ℝ) 2
          (M (ψ j) (scalarPerturbedOperator a b u - u - M c u)) :=
        (hF j).mono (by exact_mod_cast (show k ≤ n by omega))
      have hg := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
        c (ψ j) (ψ (j + 1)) (hnest j) k u
        (by simpa only [Nat.cast_add, Nat.cast_one] using houter) hforcing
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hg
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, hψ] using
    hreg (n + 1) (le_refl _) 0

end
end PositiveEinsteinFour.Geometry

end OAI

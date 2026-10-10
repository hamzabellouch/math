import OAI.Geometry.EinsteinFour.ScalarFullBallIntegerGain

namespace OAI

/-! A homogeneous scalar elliptic equation has all local integer Sobolev
orders. The zeroth-order coefficient includes the eigenvalue. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_homogeneous_all_integer_orders
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u : T) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = 0)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 r →
      MemSobolev (n : ℝ) 2 (M φ u) := by
  intro n φ hc hs
  have hg := scalar_ball_integer_forcing_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
    n c u 0 (memSobolev_fun_zero V ℂ (n : ℝ) 2) hu htest r hr0 hr1 φ hc hs
  exact hg.mono (by push_cast; linarith)

end
end PositiveEinsteinFour.Geometry

end OAI

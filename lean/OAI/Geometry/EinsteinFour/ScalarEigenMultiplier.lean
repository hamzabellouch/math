import OAI.Geometry.EinsteinFour.ScalarHomogeneousInteger

namespace OAI

/-! Absorbing the actual scalar eigenvalue into a compact zeroth-order
coefficient, on the ball where the equation is tested. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_multiplier_constant_on_test (θ ψ : S) (u : T) (κ : ℂ)
    (hθ : ∀ x ∈ tsupport (ψ : V → ℂ), θ x = κ) :
    (M θ u) ψ = κ * u ψ := by
  change u (SchwartzMap.smulLeftCLM ℂ θ ψ) = _
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth]
  change θ x * ψ x = κ * ψ x
  by_cases hx : x ∈ tsupport (ψ : V → ℂ)
  · rw [hθ x hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

theorem scalar_multiplier_add (c θ : S) (u : T) : M (c + θ) u = M c u + M θ u := by
  change smulLeftCLM ℂ ((c : V → ℂ) + (θ : V → ℂ)) u = _
  rw [smulLeftCLM_add c.hasTemperateGrowth θ.hasTemperateGrowth]
  rfl

theorem scalar_eigen_all_integer_orders
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c θ : S) (κ : ℂ) (hθ : ∀ x ∈ ball (0 : V) 1, θ x = κ)
    (u : T) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = κ * u ψ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 r →
      MemSobolev (n : ℝ) 2 (M φ u) := by
  apply scalar_homogeneous_all_integer_orders a b δ hδ ha ha1 ha2 hb hb1 hsmall
    (c + θ) u hu _ r hr0 hr1
  intro ψ hc hs
  have he := htest ψ hc hs
  rw [scalar_multiplier_add]
  simp only [sub_apply, add_apply] at he ⊢
  rw [scalar_multiplier_constant_on_test θ ψ u κ (fun x hx => hθ x (hs hx))]
  linear_combination he

end
end PositiveEinsteinFour.Geometry

end OAI

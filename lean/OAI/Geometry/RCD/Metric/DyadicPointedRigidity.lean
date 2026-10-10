import OAI.Geometry.RCD.Metric.PointedLimitValueBound
import OAI.Geometry.RCD.Metric.EuclideanDyadicGrowthRigidity

namespace OAI

/-! # Subquadratic rigidity of pointed harmonic limits -/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_harmonic_limit_affine {n : ℕ} (hn : 0 < n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hεlim : Tendsto ε atTop (𝓝 0)) (u : ℕ → X → ℝ) (f : Euclidean n → ℝ)
    (hfc : Continuous f) (hf : InnerProductSpace.HarmonicOnNhd f univ)
    {C q : ℝ} (hC : 0 < C) (hq : 0 < q) (hq4 : q < 4)
    (hdata : ∀ j : ℕ, ∀ᶠ k in atTop,
      IsPointedApproximation (p k) 0 (r k) ((2 : ℝ)^j) (ε k) (V k) ∧
      ∀ x, dist x (p k) ≤ (2 : ℝ)^j*r k → |u k x| ≤ C*q^j)
    (hconv : ∀ j : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ x, dist x (p k) ≤ (2 : ℝ)^j*r k → |u k x-f (V k x)| < η) :
    ∀ x, f x = f 0+fderiv ℝ f 0 x := by
  apply euclidean_harmonic_affine_of_dyadic_growth hn hf hC hq hq4
  intro j
  exact pointed_limit_value_bound p r ε V hεlim u f hfc (hdata j) (hconv j)

theorem dyadic_root_growth_geometric {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    2*a*Real.sqrt ((2 : ℝ)^(j+4))*(2 : ℝ)^j ≤ (8*a)*(3 : ℝ)^j := by
  have hs (k : ℕ) : Real.sqrt ((2 : ℝ)^k) = (Real.sqrt 2)^k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [pow_succ,Real.sqrt_mul (by positivity),hk,pow_succ]
  have hq : 2*Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2 : ℝ)]
  have he : 2*a*Real.sqrt ((2 : ℝ)^(j+4))*(2 : ℝ)^j =
      (8*a)*(2*Real.sqrt 2)^j := by
    rw [pow_add,Real.sqrt_mul (by positivity),hs]
    norm_num
    rw [mul_pow]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq j) (by positivity)

end RegularPointCoordinates

end

end OAI

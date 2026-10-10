import OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries
import OAI.NumberTheory.PiExponent.Analysis.CollisionExponential
import OAI.NumberTheory.PiExponent.Analysis.CollisionLimit

namespace OAI

open scoped BigOperators

namespace PiExponent.AnalyticCollision

theorem translated_row_determinant_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ) (hD : 0 ≤ D)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hss : s * s = 1 / 2)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f a j z‖ ≤ D)
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, (2 : ℝ) ^ ell i)) *
        s ^ (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  let B : ι → ℕ → ℂ := fun i d => rowTest (ell i)
    (fun t => ((center i + Complex.log (1 + t)) / (R : ℂ)) ^ d)
  let C : κ → ℕ → ι → ℂ := fun a d j => normalizedTaylorCoeff (f a j) R d
  apply Collision.infinite_collision_bound group B C D s (fun i => (2 : ℝ) ^ ell i)
    hD hs0 hs1 (fun _ => by positivity)
  · intro a d j
    exact norm_normalizedTaylorCoeff_le (by exact_mod_cast hR) (hfD a j) d
  · intro i d
    dsimp [B]
    rw [hss]
    exact norm_rowTest_shifted_power_le (by exact_mod_cast hR) (hc i) (ell i) d
  · intro i j
    exact hasSum_translated_row (hf (group i) j) hR hD (hfD (group i) j) (hc i) (ell i)

theorem translated_row_determinant_bound_sum_order
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ) (hD : 0 ≤ D)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hss : s * s = 1 / 2)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f a j z‖ ≤ D)
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (2 : ℝ) ^ (∑ i, ell i)) *
        s ^ (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  simpa only [Finset.prod_pow_eq_pow_sum] using
    translated_row_determinant_bound group f center ell R hR D s hD hs0 hs1 hss hf hfD hc

theorem translated_row_determinant_exp_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H A v : ℝ} (hH : 0 < H)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f a j z‖ ≤ Real.exp (H * A))
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ i, ell i : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (A + Real.log 2 / v + Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hfinite := translated_row_determinant_bound_sum_order group f center ell R hR
    (Real.exp (H * A)) Collision.collisionRatio (Real.exp_pos _).le
    Collision.collisionRatio_pos.le Collision.collisionRatio_lt_one
    Collision.collisionRatio_mul_self hf hfD hc
  exact hfinite.trans (Collision.collision_factor_le_exp_normalized (Fintype.card ι)
    (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) (∑ i, ell i)
    hH hell (Collision.twice_collision_count_eq group))

end PiExponent.AnalyticCollision

end OAI

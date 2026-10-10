import OAI.Geometry.RCD.Harmonic.GramDirectionalError
import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # From component gradient bounds to every constant direction -/

open Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A finite family with uniformly bounded squared gradients gives the
corresponding bound on every linear combination. -/
theorem gamma_column_le_of_diagonal_bounds {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (S : Set X) (B : ℝ)
    (hb : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x ≤ B ^ 2)
    (v : Euclidean n) :
    ∀ᵐ x ∂μ.restrict S,
      localGamma μ hQ (sobolevColumnMap μ hQ u v) (sobolevColumnMap μ hQ u v) x ≤
        ((n : ℝ) * B) ^ 2 * ‖v‖ ^ 2 := by
  have hentry (i j : Fin n) : ∀ᵐ x ∂μ.restrict S,
      |localGamma μ hQ (u i) (u j) x| ≤ B ^ 2 := by
    filter_upwards [ae_restrict_of_ae (localGamma_abs_le μ hQ (u i) (u j)),
      ae_restrict_of_ae (localGamma_self μ hQ (u i)),
      ae_restrict_of_ae (localGamma_self μ hQ (u j)), hb i, hb j]
      with x hxy hi hj hbi hbj
    rw [hi] at hbi
    rw [hj] at hbj
    nlinarith [sq_nonneg (SobolevSpace.minimalSlope μ hQ (u i) x -
      SobolevSpace.minimalSlope μ hQ (u j) x)]
  have hall : ∀ᵐ x ∂μ.restrict S, ∀ i j : Fin n,
      |localGamma μ hQ (u i) (u j) x| ≤ B ^ 2 := by
    suffices hh : ∀ᵐ x ∂μ.restrict S, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ∀ j ∈ (Finset.univ : Finset (Fin n)),
          |localGamma μ hQ (u i) (u j) x| ≤ B ^ 2 by
      simpa only [Finset.mem_univ, forall_true_left] using hh
    exact (Filter.eventually_all_finset Finset.univ).mpr fun i _ =>
      (Filter.eventually_all_finset Finset.univ).mpr fun j _ => hentry i j
  filter_upwards [hall, ae_restrict_of_ae (localGamma_column_pair μ hQ u v v)] with x hx he
  rw [he]
  have hterm (i j : Fin n) : (v i * v j) * localGamma μ hQ (u i) (u j) x ≤
      ‖v‖ ^ 2 * B ^ 2 := by
    have hi : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have hj : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have hv : |v i * v j| ≤ ‖v‖ ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
    calc
      _ ≤ |(v i * v j) * localGamma μ hQ (u i) (u j) x| := le_abs_self _
      _ = |v i * v j| * |localGamma μ hQ (u i) (u j) x| := abs_mul _ _
      _ ≤ _ := mul_le_mul hv (hx i j) (abs_nonneg _) (sq_nonneg _)
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖v‖ ^ 2 * B ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp; ring

/-- The first-order splitting definition controls the gradient of every
constant direction, not merely the coordinate columns. -/
theorem FirstOrderSplittingOn.directional_gradient {n : ℕ} {p : X} {r ε : ℝ}
    {u : Fin n → SobolevSpace μ hQ} {w : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p r ε u w) (v : Euclidean n) :
    ∀ᵐ x ∂μ.restrict (Metric.ball p r),
      localGamma μ hQ (sobolevColumnMap μ hQ u v) (sobolevColumnMap μ hQ u v) x ≤
        ((n : ℝ) * (1 + ε)) ^ 2 * ‖v‖ ^ 2 :=
  gamma_column_le_of_diagonal_bounds μ hQ u _ (1 + ε) h.gradient v

end RegularPointCoordinates

end

end OAI

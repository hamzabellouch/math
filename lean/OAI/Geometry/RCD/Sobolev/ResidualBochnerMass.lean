import OAI.Geometry.RCD.Sobolev.BochnerMassFromEnergy
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # Small full mass for a residual with small gradient -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Testing the full Bochner equation with the actual good cutoff converts
an upper bound for the residual gradient into small mass on the inner ball. -/
theorem GoodLaplacianCutoff.mass_le_of_gradient
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r ρ C β : ℝ} {L : ℝ≥0} {v : E}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (_hρ : 0 < ρ) (hρr : ρ < r)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (hgradient : ∀ᵐ x ∂μ.restrict (closedBall p (2 * ρ)),
      localGamma μ hQ (U v) (U v) x ≤ β) :
    ⟪v, M.massOperator (ball p ρ) v⟫_ℝ ≤
      ((C / ρ ^ 2) / 2 + κ) * β * μ.real (closedBall p (2 * ρ)) := by
  let : IsFiniteMeasure (μ.restrict (closedBall p (2 * ρ))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_closedBall p (2 * ρ)).measure_lt_top⟩
  have henergy : (∫ x in closedBall p (2 * ρ), localGamma μ hQ (U v) (U v) x ∂μ) ≤
      β * μ.real (closedBall p (2 * ρ)) := by
    calc
      _ ≤ ∫ _x in closedBall p (2 * ρ), β ∂μ :=
        integral_mono_ae (localGamma_memL1 μ hQ (U v) (U v)).integrableOn
          (integrable_const _) hgradient
      _ = _ := by
        simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm]
  have hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → χ.laplacian x = 0 := by
    filter_upwards [χ.laplacian_locality] with x hx hnot
    apply hx
    right
    have hdist : 2 * r ≤ dist p x := by
      simpa only [mem_ball, dist_comm, not_lt] using hnot
    linarith
  have hqS : ∀ᵐ x ∂μ, x ∉ closedBall p (2 * ρ) → χ.laplacian x = 0 := by
    filter_upwards [χ.laplacian_locality] with x hx hnot
    apply hx
    right
    simpa only [mem_closedBall, dist_comm, not_le] using hnot
  have hb := G.mass_le_of_energy μ hQ χ.weight χ.bounds (χ.hasCompactSupport μ hQ)
    (fun x hx => by
      exact lt_of_le_of_lt (χ.tsupport_subset μ hQ hx)
        (show 2 * ρ < 2 * r by linarith))
    χ.sobolev χ.representative χ.laplacian χ.weak_laplacian hqs
    (closedBall p (2 * ρ)) (ball p ρ) measurableSet_ball χ.one
    (fun x hx => χ.zero x (by simpa only [mem_closedBall, dist_comm, not_le] using hx))
    hqS (div_nonneg hC (sq_nonneg ρ)) hκ χ.laplacian_bound henergy
  simpa only [mul_assoc] using hb

end RegularPointCoordinates

end

end OAI

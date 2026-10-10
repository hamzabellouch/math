import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-!
# Scaled Bochner mass from a first-order splitting map

This connects the actual averaged component errors in the splitting
hypothesis to the dimensionless full mass used in the metric iteration.
-/

open Set Metric MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- Restricting the averaged error on the large harmonic ball controls
the unnormalized error on every closed interior ball. -/
theorem FirstOrderSplittingOn.closed_error_le {n : ℕ} {p : X} {r ε R : ℝ}
    {u : Fin n → SobolevSpace μ hQ} {w : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p r ε u w) (hR : R < r)
    (hvol : 0 < μ.real (ball p r)) (hfinite : μ (ball p r) ≠ ∞) (i j : Fin n) :
    (∫ x in closedBall p R,
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ) ≤
      ε * μ.real (ball p r) := by
  have havg : (∫ x in ball p r,
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ) ≤
      ε * μ.real (ball p r) := by
    apply (div_le_iff₀ hvol).mp
    simpa only [div_eq_inv_mul] using h.gram i j
  have hsub : closedBall p R ⊆ ball p r := fun x hx => lt_of_le_of_lt hx hR
  have hi : IntegrableOn (fun x =>
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)|) (ball p r) μ :=
    ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub (integrableOn_const hfinite)).abs
  exact (setIntegral_mono_set hi (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall hsub)).trans havg

/-- The normalized full Bochner mass is small when the splitting error
and the rescaled curvature are small. -/
theorem splitting_normalized_bochner_mass_le [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} {p : X} {r ε C κ : ℝ} {L : ℝ≥0}
    {u : Fin n → SobolevSpace μ hQ} {w : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p (8 * r) ε u w)
    (hr : 0 < r) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hvol : 0 < μ.real (ball p (8 * r)))
    (χ : GoodLaplacianCutoff μ hQ p (r / 2) C)
    (M : PositiveBilinearMeasure X (Euclidean n))
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p r L v)
    (v : Euclidean n) :
    (r ^ 2 / μ.real (ball p (8 * r))) * ⟪v, M.massOperator (ball p (r / 2)) v⟫_ℝ ≤
      (2 * C * (n : ℝ) ^ 2 * ε + κ * r ^ 2 * ((n : ℝ) ^ 2 * ε + 1)) * ‖v‖ ^ 2 := by
  let V := μ.real (ball p (8 * r))
  have hfinite' : μ (ball p (8 * r)) ≠ ∞ :=
    ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall p (8 * r)).measure_lt_top)
  have herr : ∀ i j : Fin n, ∫ x in closedBall p (2 * (r / 2)),
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ ε * V := by
    intro i j
    exact h.closed_error_le μ hQ (by linarith) hvol hfinite' i j
  have hb := χ.harmonic_mass_le μ hQ (half_pos hr) (by linarith) hC hκ u M G
    (mul_nonneg hε hvol.le) herr v
  have hrad : 2 * (r / 2) = r := by ring
  rw [hrad] at hb
  have hsub : closedBall p r ⊆ ball p (8 * r) := by
    intro x hx
    change dist x p < 8 * r
    have hd : dist x p ≤ r := hx
    linarith
  have hW : μ.real (closedBall p r) ≤ V := measureReal_mono hsub hfinite'
  have hcoef : (C / (r / 2) ^ 2) * ((n : ℝ) ^ 2 * (ε * V)) / 2 +
      κ * ((n : ℝ) ^ 2 * (ε * V) + μ.real (closedBall p r)) ≤
      (C / (r / 2) ^ 2) * ((n : ℝ) ^ 2 * (ε * V)) / 2 +
      κ * ((n : ℝ) ^ 2 * (ε * V) + V) := by
    nlinarith [mul_le_mul_of_nonneg_left hW hκ]
  have hB := hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖v‖))
  have hscale := mul_le_mul_of_nonneg_left hB (div_nonneg (sq_nonneg r) hvol.le)
  refine hscale.trans_eq ?_
  change (r ^ 2 / V) * (_ * ‖v‖ ^ 2) = _
  have hV : V ≠ 0 := ne_of_gt hvol
  field_simp [hV, ne_of_gt hr]

end RegularPointCoordinates

end

end OAI

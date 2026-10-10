import OAI.Geometry.RCD.Transport.LocalBochnerTransport
import OAI.Geometry.RCD.Heat.DyadicHeatFamily
import OAI.Geometry.RCD.Heat.RelativeHeatMean

namespace OAI

/-! # Converting the actual normalized Bochner bound to heat smallness -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The normalized Bochner estimate on a sixteen-times larger ball gives
smallness in a heat metric at the inner scale. Both comparison factors are
two, so they cancel the factor four from the Bochner cutoff radius. -/
theorem bochner_mass_small_relative_to_heat {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (M : PositiveBilinearMeasure X (Euclidean n))
    {p : X} {s R e C κ V : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p (2 * s) L v)
    (A : Euclidean n ≃L[ℝ] Euclidean n) {w : X → Euclidean n}
    (hfirst : FirstOrderSplittingOn μ hQ p (16 * s) e (transformedColumn μ hQ u A) w)
    (hexact : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
      (ball p (16 * s)) measurableSet_ball A)
    (hs : 0 < s) (hsR : s ≤ R) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hcurv : κ * R ^ 2 ≤ e) (hV : 0 ≤ V)
    (hvolpos : 0 < μ.real (ball p (16 * s)))
    (hvol : μ.real (ball p (16 * s)) ≤ V * (16 * s) ^ n)
    (χ : GoodLaplacianCutoff μ hQ p s C)
    (Q : Euclidean n →L[ℝ] Euclidean n) (hQpos : Q.IsPositive)
    (hcoarse : ∀ v, ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u)
      (ball p (16 * s)) measurableSet_ball v⟫_ℝ ≤
        2 * ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u)
          (ball p s) measurableSet_ball v⟫_ℝ)
    (hheat : ∀ v, ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u)
      (ball p s) measurableSet_ball v⟫_ℝ ≤ 2 * ⟪v, Q v⟫_ℝ)
    (v : Euclidean n) :
    (s ^ 2 / s ^ n) * ⟪v, M.massOperator (ball p s) v⟫_ℝ ≤
      (V * (16 : ℝ) ^ n * (2 * C * (n : ℝ) ^ 2 + 4 * ((n : ℝ) ^ 2 + 1))) * e * ⟪v, Q v⟫_ℝ := by
  have h16 : 8 * (2 * s) = 16 * s := by ring
  have hhalf : (2 * s) / 2 = s := by ring
  have hb := original_gram_bochner_mass_le μ hQ u M G A
    (by simpa only [h16] using hfirst) (by simpa only [h16] using hexact)
    (by positivity : 0 < 2 * s) he hC hκ
    (by simpa only [h16] using hvolpos)
    (by simpa only [hhalf] using χ) v
  simp only [h16, hhalf] at hb
  let budget := 2 * C * (n : ℝ) ^ 2 * e + κ * (2 * s) ^ 2 * ((n : ℝ) ^ 2 * e + 1)
  have hbudget : 0 ≤ budget := by dsimp only [budget]; positivity
  have hmean : ⟪v, sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u)
      (ball p (16 * s)) measurableSet_ball v⟫_ℝ ≤ 4 * ⟪v, Q v⟫_ℝ := by
    linarith [hcoarse v, hheat v]
  have hbm := hb.trans (mul_le_mul_of_nonneg_left hmean hbudget)
  have hκs : κ * s ^ 2 ≤ e := by
    have hsq := (sq_le_sq₀ hs.le (hs.le.trans hsR)).mpr hsR
    exact (mul_le_mul_of_nonneg_left hsq hκ).trans hcurv
  have hbudgetUpper : budget ≤ (2 * C * (n : ℝ) ^ 2 + 4 * ((n : ℝ) ^ 2 + 1)) * e := by
    have hne := mul_le_mul_of_nonneg_left he1 (sq_nonneg (n : ℝ))
    have hprod := mul_le_mul hκs (show (n : ℝ) ^ 2 * e + 1 ≤ (n : ℝ) ^ 2 + 1 by linarith)
      (by positivity : 0 ≤ (n : ℝ) ^ 2 * e + 1) he
    dsimp only [budget]
    nlinarith only [hprod]
  have hVratio : μ.real (ball p (16 * s)) / (4 * s ^ n) ≤ V * (16 : ℝ) ^ n / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * s ^ n)).mpr
    convert hvol using 1; ring
  have hidentity : (s ^ 2 / s ^ n) * ⟪v, M.massOperator (ball p s) v⟫_ℝ =
      (μ.real (ball p (16 * s)) / (4 * s ^ n)) *
        (((2 * s) ^ 2 / μ.real (ball p (16 * s))) * ⟪v, M.massOperator (ball p s) v⟫_ℝ) := by
    generalize μ.real (ball p (16 * s)) = volume at hvolpos ⊢
    field_simp [hs.ne', hvolpos.ne']
    ring
  rw [hidentity]
  calc
    _ ≤ (μ.real (ball p (16 * s)) / (4 * s ^ n)) * (budget * (4 * ⟪v, Q v⟫_ℝ)) :=
      mul_le_mul_of_nonneg_left hbm (by positivity)
    _ ≤ (V * (16 : ℝ) ^ n / 4) * (budget * (4 * ⟪v, Q v⟫_ℝ)) :=
      mul_le_mul_of_nonneg_right hVratio (mul_nonneg hbudget (mul_nonneg (by norm_num) (hQpos.inner_nonneg_right v)))
    _ ≤ (V * (16 : ℝ) ^ n / 4) *
        (((2 * C * (n : ℝ) ^ 2 + 4 * ((n : ℝ) ^ 2 + 1)) * e) * (4 * ⟪v, Q v⟫_ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbudgetUpper
        (mul_nonneg (by norm_num) (hQpos.inner_nonneg_right v))) (by positivity)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI

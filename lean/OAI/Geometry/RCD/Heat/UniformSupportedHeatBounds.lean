import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.SupportedHeatEnvelope
import OAI.Geometry.RCD.Heat.UniformHeatMassIncrement

namespace OAI

/-! # Decrement constants chosen before the harmonic coordinates and mass -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- With fixed cutoff support, Gaussian constants give a common two-sided
decrement constant before choosing the harmonic column, its full Bochner
measure, the pole or the cutoff. This order permits subsequent mass absorption. -/
theorem exists_uniform_supported_heat_bound (m : ℕ) (hg : HasCoordinateHeatBounds μ ker)
    {Vlo Vhi η lambda : ℝ}
    (hVlo : 0 < Vlo) (hVhi : 0 < Vhi) (hη : 0 ≤ η) (hlambda : 0 < lambda) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (hR : 0 < R), R ≤ 1 → ∀ (p : X) (r κ : ℝ) (L : ℝ≥0)
        (U : Euclidean (m + 2) →L[ℝ] SobolevSpace μ hQ)
        (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
        (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
        (ρ Ccut : ℝ) (χ : GoodLaplacianCutoff μ hQ p ρ Ccut),
        0 < ρ → ρ < r → 0 ≤ κ → 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda →
        (∀ y ∈ ball p (R / 4), (χ.weight : X → ℝ) y = 1) →
        (∀ y ∉ ball p R, (χ.weight : X → ℝ) y = 0) →
        (∀ i : ℕ, ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          ∀ y ∈ ball p (R / 2 ^ i), 0 < μ.real (ball y (Real.sqrt t)) ∧
            μ.real (ball y (Real.sqrt t)) ≤ Vhi * (R / 2 ^ i) ^ (m + 2)) →
        (∀ i : ℕ, ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          ∀ y, (χ.weight : X → ℝ) y ≠ 0 →
            Vlo * (R / 2 ^ i) ^ (m + 2) ≤ μ.real (ball y (Real.sqrt t))) →
        ∀ i, 2 ≤ i →
        (∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
          ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η) →
        ∀ v : Euclidean (m + 2),
          let d := ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i :
              Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)) -
            (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) :
              Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))) v⟫_ℝ
          0 ≤ d ∧ ⟪v, dyadicBochnerMass M (m + 2) p R i v⟫_ℝ ≤ C * d ∧
            d ≤ C * ⟪v, dyadicBochnerEnvelope M (m + 2) p R i v⟫_ℝ := by
  obtain ⟨A, D, hA, hD, hupper⟩ := cutoff_gaussian_block_bound μ hg (m + 2) hVlo
  obtain ⟨c, hc, hlower⟩ := uniform_gaussian_lower_time_block μ hg (m + 2) hVhi
    (show (0 : ℝ) ≤ 1 by norm_num)
  let B := supportedHeatEnvelopeConstant m A D 1 lambda η
  let a := 3 * c / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hB : 0 ≤ B := supportedHeatEnvelopeConstant_nonneg m hA.le (add_nonneg hlambda.le hη)
  refine ⟨1 + B + a⁻¹, by positivity, ?_⟩
  intro R hR hR1 p r κ L U M G ρ Ccut χ hρ hρr hκ hreg hχone hχzero hvolhi hvollo i hi herr v
  have hBcompare : supportedHeatEnvelopeConstant m A D R lambda η ≤ B := by
    have hs := mul_le_mul_of_nonneg_right ((sq_le_sq₀ hR.le zero_le_one).mpr hR1)
      (add_nonneg hlambda.le hη)
    dsimp only [supportedHeatEnvelopeConstant, B]
    norm_num at hs ⊢
    nlinarith only [hs]
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hsR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hs1 := hsR.trans hR1
  have hsone : R / (2 : ℝ) ^ i ≤ R / 4 := by
    have hp : (4 : ℝ) ≤ 2 ^ i := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi
      norm_num at h ⊢
      exact h
    exact div_le_div_of_nonneg_left hR.le (by norm_num) hp
  have hlow := dyadicHeatGram_lower μ hQ hk χ G hρ hρr hκ hR hlambda hreg i
    (fun y hy => hχone y (ball_subset_ball hsone hy)) herr
    (fun t ht => hlower _ hs hs1 p (ball p (R / 2 ^ i))
      (fun t ht1 ht2 => hvolhi i t ⟨ht1, ht2⟩)
      (fun y hy => by
        have hd : dist p y < R / 2 ^ i := by simpa only [mem_ball, dist_comm] using hy
        nlinarith [dist_nonneg (x := p) (y := y)]) t ht.1 ht.2) v
  have hupp := dyadicHeatGram_upper_supported μ hQ hk G χ m rfl hρ hρr hκ hR hlambda
    hA.le hD hη hreg i hχzero herr
    (fun t ht => hupper _ t hs hs1
      ((div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1) ht.2 p
      χ.weight χ.bounds (hvollo i t ht)) v
  dsimp only
  let d := ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i :
      Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)) -
    (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) :
      Euclidean (m + 2) →L[ℝ] Euclidean (m + 2))) v⟫_ℝ
  change a * ⟪v, dyadicBochnerMass M (m + 2) p R i v⟫_ℝ ≤ d at hlow
  change d ≤ supportedHeatEnvelopeConstant m A D R lambda η *
    ⟪v, dyadicBochnerEnvelope M (m + 2) p R i v⟫_ℝ at hupp
  have hN := (dyadicBochnerMass_isPositive M (m + 2) p hR.le i).inner_nonneg_right v
  have hF := (dyadicBochnerEnvelope_isPositive M (m + 2) p hR.le i).inner_nonneg_right v
  have hd : 0 ≤ d := (mul_nonneg ha.le hN).trans hlow
  have hlow' : ⟪v, dyadicBochnerMass M (m + 2) p R i v⟫_ℝ ≤ a⁻¹ * d := by
    have h := mul_le_mul_of_nonneg_left hlow (inv_pos.mpr ha).le
    simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using h
  refine ⟨hd, hlow'.trans ?_, hupp.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hd
    linarith
  · apply mul_le_mul_of_nonneg_right _ hF
    linarith [inv_nonneg.mpr ha.le]

end RegularPointCoordinates

end

end OAI

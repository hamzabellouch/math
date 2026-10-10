import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.DyadicHeatFamily

namespace OAI

/-! # A uniform two-sided decrement bound for the actual heat family -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ r : ℝ} {p : X} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ Ccut : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ Ccut)

/-- The published Gaussian bound, volume bounds and the actual annular
error estimate imply both decrement bounds with one constant. In particular,
the envelope and the lower mass are constructed from the same full measure. -/
theorem uniform_dyadic_heat_bounds (hg : HasCoordinateHeatBounds μ ker)
    (m : ℕ) (hn : n = m + 2) (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R Vlo Vhi η lambda : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hVlo : 0 < Vlo) (hVhi : 0 < Vhi) (hη : 0 ≤ η) (hlambda : 0 < lambda)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda)
    (hχone : ∀ y ∈ ball p R, (χ.weight : X → ℝ) y = 1)
    (herror : ∀ t, 0 < t → t ≤ R ^ 2 → ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hvolhi : ∀ i : ℕ, ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ y ∈ ball p (R / 2 ^ i),
        0 < μ.real (ball y (Real.sqrt t)) ∧
          μ.real (ball y (Real.sqrt t)) ≤ Vhi * (R / 2 ^ i) ^ n)
    (hvollo : ∀ i : ℕ, ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ y, (χ.weight : X → ℝ) y ≠ 0 →
        Vlo * (R / 2 ^ i) ^ n ≤ μ.real (ball y (Real.sqrt t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ i (v : Euclidean n),
      let d := ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ
      0 ≤ d ∧ ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤ C * d ∧
        d ≤ C * ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ := by
  obtain ⟨A, D, hA, hD, hupper⟩ := cutoff_gaussian_block_bound μ hg n hVlo
  obtain ⟨c, hc, hlower⟩ := uniform_gaussian_lower_time_block μ hg n hVhi
    (show (0 : ℝ) ≤ 1 by norm_num)
  let B := dyadicHeatEnvelopeConstant M m A D R lambda η
  let a := 3 * c / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hB : 0 ≤ B := dyadicHeatEnvelopeConstant_nonneg M m hA.le hR.le (add_nonneg hlambda.le hη)
  refine ⟨1 + B + a⁻¹, by positivity, ?_⟩
  intro i v
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hsR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hs1 := hsR.trans hR1
  have herr : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η := by
    intro t ht
    exact herror t ((div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1)
      (ht.2.trans ((sq_le_sq₀ hs.le hR.le).mpr hsR))
  have hlow := dyadicHeatGram_lower μ hQ hk χ G hρ hρr hκ hR hlambda hreg i
    (fun y hy => hχone y (ball_subset_ball hsR hy)) herr
    (fun t ht => hlower _ hs hs1 p (ball p (R / 2 ^ i))
      (fun t ht1 ht2 => hvolhi i t ⟨ht1, ht2⟩)
      (fun y hy => by
        have hd : dist p y < R / 2 ^ i := by simpa only [mem_ball, dist_comm] using hy
        nlinarith [dist_nonneg (x := p) (y := y)]) t ht.1 ht.2) v
  have hupp := dyadicHeatGram_upper μ hQ hk χ G m hn hρ hρr hκ hR hlambda hA.le hD hη hreg i herr
    (fun t ht => hupper _ t hs hs1
      ((div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)).trans_le ht.1) ht.2 p
      χ.weight χ.bounds (hvollo i t ht)) v
  dsimp only
  let d := ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
    (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ
  change a * ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤ d at hlow
  change d ≤ B * ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ at hupp
  have hN := (dyadicBochnerMass_isPositive M n p hR.le i).inner_nonneg_right v
  have hF := (dyadicBochnerEnvelope_isPositive M n p hR.le i).inner_nonneg_right v
  have hd : 0 ≤ d := (mul_nonneg ha.le hN).trans hlow
  have hlow' : ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤ a⁻¹ * d := by
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

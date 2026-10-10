import OAI.Geometry.RCD.Heat.ActualHeatEnvelope
import OAI.Geometry.RCD.Heat.UniformHeatMassIncrement

namespace OAI

/-! # Actual dyadic heat Gram equivalences and their two decrement bounds -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

theorem dyadic_radius_square_succ (R : ℝ) (i : ℕ) :
    (R / (2 : ℝ) ^ (i + 1)) ^ 2 = (R / (2 : ℝ) ^ i) ^ 2 / 4 := by
  rw [pow_succ]
  field_simp
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} (U : Euclidean n →L[ℝ] SobolevSpace μ hQ)
  {p : X} {ρ Ccut : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ Ccut)

/-- All dyadic heat metrics are the actual regularized heat Grams of one
fixed coordinate span, cutoff and pole. -/
def dyadicHeatGram {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda) (i : ℕ) :
    Euclidean n ≃L[ℝ] Euclidean n :=
  cutoffHeatGramEquiv μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
    U (fun z => (χ.bounds z).1)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ i from div_pos hR (by positivity))) p hlambda

theorem cutoffHeatGram_time_congr {s t lambda : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s = t) :
    cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) U hs p lambda =
      cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ) U ht p lambda := by
  subst t
  rfl

theorem dyadicHeatGram_coe {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda) (i : ℕ) :
    (dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) =
      cutoffHeatGram μ hQ hk χ.weight.continuous (χ.hasCompactSupport μ hQ)
        U (sq_pos_of_pos (div_pos hR (show 0 < (2 : ℝ) ^ i by positivity))) p lambda := rfl

theorem dyadicHeatGram_isPositive {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (i : ℕ) :
    (dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n).IsPositive := by
  rw [dyadicHeatGram_coe]
  exact cutoffHeatGram_isPositive μ hQ hk _ _ U (fun z => (χ.bounds z).1) _ p hlambda.le

variable {U} {M : PositiveBilinearMeasure X (Euclidean n)} {κ r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)

/-- The lower decrement controls exactly the dyadic full Bochner mass. -/
theorem dyadicHeatGram_lower (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R c η lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda) (i : ℕ)
    (hχone : ∀ y ∈ ball p (R / 2 ^ i), (χ.weight : X → ℝ) y = 1)
    (herror : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hkernel : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ y ∈ ball p (R / 2 ^ i), c / (R / 2 ^ i) ^ n ≤ ker t p y)
    (v : Euclidean n) :
    (3 * c / 2) * ⟪v, dyadicBochnerMass M n p R i v⟫_ℝ ≤
      ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ := by
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hb := dyadic_heat_increment_lower_mass μ hQ hk G χ hρ hρr hκ
    (ball p (R / 2 ^ i)) measurableSet_ball hχone hs hlambda.le hreg herror hkernel v
  have hnext := cutoffHeatGram_time_congr μ hQ hk U χ (lambda := lambda)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ (i + 1) from div_pos hR (by positivity)))
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) (dyadic_radius_square_succ R i)
  simp only [dyadicBochnerMass_inner, M.measure_real v _ measurableSet_ball,
    sub_apply, inner_sub_right, dyadicHeatGram_coe]
  rw [hnext]
  convert hb using 1
  ring

/-- The upper decrement has the same fixed-root mass envelope at every
index, with one constant independent of the index and direction. -/
theorem dyadicHeatGram_upper (m : ℕ) (hn : n = m + 2)
    (hρ : 0 < ρ) (hρr : ρ < r) (hκ : 0 ≤ κ)
    {R A D η lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hA : 0 ≤ A) (hD : 0 < D) (hη : 0 ≤ η)
    (hreg : 2 * κ * (L : ℝ) ^ 2 + η ≤ lambda) (i : ℕ)
    (herror : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ‖harmonicHeatError μ hQ (k := ker) G χ t p‖ ≤ η)
    (hgaussian : ∀ t ∈ Icc ((R / 2 ^ i) ^ 2 / 4) ((R / 2 ^ i) ^ 2),
      ∀ q : ℝ, 0 ≤ q → ∀ z, q * (R / 2 ^ i) ≤ dist p z →
        (χ.weight : X → ℝ) z * ker t p z ≤
          (A / (R / 2 ^ i) ^ n) * Real.exp (-q ^ 2 / D)) (v : Euclidean n) :
    ⟪v, ((dyadicHeatGram μ hQ hk U χ hR hlambda i : Euclidean n →L[ℝ] Euclidean n) -
        (dyadicHeatGram μ hQ hk U χ hR hlambda (i + 1) : Euclidean n →L[ℝ] Euclidean n)) v⟫_ℝ ≤
      dyadicHeatEnvelopeConstant M m A D R lambda η * ⟪v, dyadicBochnerEnvelope M n p R i v⟫_ℝ := by
  have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hroot : (2 : ℝ) ^ i * (R / (2 : ℝ) ^ i) = R := by field_simp
  have hb := gaussian_dyadic_heat_increment_envelope μ hQ hk G χ m hρ hρr hκ
    hs hA hD hη hlambda.le hreg herror (by simpa only [← hn] using hgaussian) i hroot v
  have hnext := cutoffHeatGram_time_congr μ hQ hk U χ (lambda := lambda)
    (sq_pos_of_pos (show 0 < R / (2 : ℝ) ^ (i + 1) from div_pos hR (by positivity)))
    (div_pos (sq_pos_of_pos hs) (by norm_num : (0 : ℝ) < 4)) (dyadic_radius_square_succ R i)
  simp only [sub_apply, inner_sub_right, dyadicHeatGram_coe]
  rw [hnext]
  simpa only [← hn] using hb

end RegularPointCoordinates

end

end OAI

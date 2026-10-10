import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.LongAverageHeatBound
import OAI.Geometry.RCD.Metric.SupportedAverageDifference
import OAI.Geometry.RCD.Metric.ShortAverageMass

namespace OAI

/-! # The full positive-source difference on one long-time block -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

/-- Every long-time block has the displacement factor r/s multiplying
its actual full-mass envelope at scale s. -/
theorem exists_long_average_mass_bound (hg : HasCoordinateHeatBounds μ ker)
    (hdiff : HasGaussianHeatDifferenceBounds μ ker)
    (m : ℕ) {A V : ℝ} (hA : 0 ≤ A) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : PositiveBilinearMeasure X (Euclidean (m + 2)))
      (R : ℝ) (_hR : 0 < R), R ≤ 1 → ∀ (x : X) (χ : X →ᵇ ℝ),
      ∀ hcompact : HasCompactSupport (χ : X → ℝ), (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
      (∀ z ∉ ball x R, χ z = 0) → ∀ (j : ℕ) (r : ℝ) (q : X),
      0 < r → r ≤ (R / 2 ^ j) / 2 → μ (ball q r) ≠ ∞ →
      0 < μ.real (ball q r) → dist x q ≤ A * r →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ Icc ((R / 2 ^ j) ^ 2 / 4) ((R / 2 ^ j) ^ 2) →
      (∀ z, χ z ≠ 0 → V * (Real.sqrt t) ^ (m + 2) ≤ μ.real (ball z (Real.sqrt t))) →
      ∀ v : Euclidean (m + 2),
      (R / 2 ^ j) ^ 2 * |⟪v,
        (cutoffAverageHeatMass μ hQ hk χ.continuous hcompact M ht (ball q r) measurableSet_ball isBounded_ball -
         cutoffHeatMass μ hQ hk χ.continuous hcompact M ht x) v⟫_ℝ| ≤
        C * (r / (R / 2 ^ j)) * ⟪v, dyadicBochnerEnvelope M (m + 2) x R j v⟫_ℝ := by
  obtain ⟨C₀, D, hC₀, hD, hbound⟩ := exists_long_average_difference_bound μ hQ hk hg hdiff (m + 2) hA hV
  let G := gaussianMassConvolutionConstant m D⁻¹
  let B := C₀ * (2 : ℝ) ^ (m + 3)
  have hG : 0 ≤ G := gaussianMassConvolutionConstant_nonneg _ _
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B * (G + 1), by positivity, ?_⟩
  intro M R hR hR1 x χ hcompact hχ hzero j r q hr hrs hfinite hvol hcenter t ht htime hsource v
  let s := R / (2 : ℝ) ^ j
  have hs : 0 < s := div_pos hR (by positivity)
  have hsR : s ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hsqrt : s / 2 ≤ Real.sqrt t := by
    have hsq := Real.sq_sqrt ht.le
    have hs0 := Real.sqrt_nonneg t
    change s ^ 2 / 4 ≤ t ∧ t ≤ s ^ 2 at htime
    nlinarith
  have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have ht1 : t ≤ 1 := htime.2.trans (by nlinarith)
  have hrtime : r ^ 2 ≤ t := by
    have hss : 0 < s / 2 := half_pos hs
    have hh := (sq_le_sq₀ hr.le hss.le).mpr hrs
    nlinarith [htime.1]
  have hinv : (Real.sqrt t)⁻¹ ≤ 2 * s⁻¹ := by
    have h := one_div_le_one_div_of_le (half_pos hs) hsqrt
    simpa only [one_div, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul] using h
  have hpow := pow_le_pow_left₀ (inv_pos.mpr hsqrtpos).le hinv (m + 3)
  let α := B * (r / s)
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hcoef : C₀ * r * (Real.sqrt t)⁻¹ ^ (m + 3) ≤ α / s ^ (m + 2) := by
    apply (mul_le_mul_of_nonneg_left hpow (mul_pos hC₀ hr).le).trans_eq
    dsimp only [α, B]
    rw [mul_pow, show m + 3 = (m + 2) + 1 by omega, pow_succ (s⁻¹)]
    simp only [inv_pow]
    field_simp [hs.ne']
  let W := fun z => C₀ * r * (Real.sqrt t)⁻¹ ^ (m + 3) *
    Real.exp (-(dist x z) ^ 2 / (D * t))
  have hW : Continuous W := by dsimp only [W]; fun_prop
  have habs := cutoffAverageHeatMass_difference_le_supported μ hQ hk χ.continuous hcompact
    M (fun z => (hχ z).1) ht (ball q r) measurableSet_ball isBounded_ball x W hW
    (fun z hz => hbound r t x q z hr ht ht1 hrtime hfinite hvol hcenter (hsource z hz)) v
  have hpoint z : χ z * W z ≤ (α / s ^ (m + 2)) * Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) := by
    have hfrac := div_le_div_of_nonneg_left (sq_nonneg (dist x z)) (mul_pos hD ht)
      (mul_le_mul_of_nonneg_left htime.2 hD.le)
    have he : Real.exp (-(dist x z) ^ 2 / (D * t)) ≤ Real.exp (-(dist x z) ^ 2 / (D * s ^ 2)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hfrac
    have hWnonneg : 0 ≤ W z := by dsimp only [W]; positivity
    exact (mul_le_of_le_one_left hWnonneg (hχ z).2).trans
      (mul_le_mul hcoef he (Real.exp_pos _).le (div_nonneg hα (pow_pos hs _).le))
  have hroot : (2 : ℝ) ^ j * s = R := by dsimp only [s]; field_simp
  have hdisplace : ∀ a : ℝ, 0 ≤ a → ∀ z, a * s ≤ dist x z →
      χ z * W z ≤ (α / s ^ (m + 2)) * Real.exp (-a ^ 2 / D) := by
    intro a ha z hz
    have hd := (sq_le_sq₀ (mul_nonneg ha hs.le) dist_nonneg).mpr hz
    have hh := div_le_div_of_nonneg_right hd (by positivity : 0 ≤ D * s ^ 2)
    have he : (a * s) ^ 2 / (D * s ^ 2) = a ^ 2 / D := by field_simp
    rw [he] at hh
    exact (hpoint z).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hh))
      (div_nonneg hα (pow_pos hs _).le))
  have hwi : Integrable (fun z => χ z * W z) (M.measure v) :=
    (χ.continuous.mul hW).integrable_of_hasCompactSupport hcompact.mul_right
  have hi := scaled_integral_le_geometric_mass (M.measure v) m x hs hwi hα
    (inv_pos.mpr hD) le_rfl j
    (fun k _ z hz => shell_bound_of_displacement x hs _ hdisplace k hz)
    (fun z hz => by rw [hroot] at hz; simp only [hzero z hz, zero_mul]; exact le_rfl)
  let S := ∑ k ∈ Finset.range (j + 1), (3 / 4 : ℝ) ^ (j - k) *
    ⟪v, dyadicBochnerMass M (m + 2) x R k v⟫_ℝ
  have he : (∑ k ∈ Finset.range (j + 1), (3 / 4 : ℝ) ^ k *
      (((2 ^ k * s) ^ 2 / (2 ^ k * s) ^ (m + 2)) *
        (M.measure v).real (ball x (2 ^ k * s)))) = S := by
    rw [outward_sum_eq_inward_sum (fun r => (r ^ 2 / r ^ (m + 2)) *
      (M.measure v).real (ball x r)) (3 / 4) j hroot]
    simp only [S, dyadicBochnerMass_inner]
  rw [he] at hi
  simp only [mul_zero, zero_mul, add_zero] at hi
  have htotal := (mul_le_mul_of_nonneg_left habs (sq_nonneg s)).trans hi
  rw [dyadicBochnerEnvelope_inner]
  change _ ≤ B * (G + 1) * (r / s) * ((3 / 4 : ℝ) ^ j * ‖v‖ ^ 2 + S)
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ =>
    mul_nonneg (by positivity) ((dyadicBochnerMass_isPositive M (m + 2) x hR.le k).inner_nonneg_right v)
  have hp : 0 ≤ (3 / 4 : ℝ) ^ j * ‖v‖ ^ 2 := by positivity
  change _ ≤ α * G * S at htotal
  rw [show B * (G + 1) * (r / s) = α * (G + 1) by dsimp only [α]; ring]
  nlinarith only [htotal, mul_nonneg (mul_nonneg hα (by linarith : 0 ≤ G + 1)) hp,
    mul_nonneg hα hS]

end RegularPointCoordinates

end

end OAI

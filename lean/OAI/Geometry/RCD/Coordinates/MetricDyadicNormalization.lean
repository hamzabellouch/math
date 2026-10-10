import OAI.Geometry.RCD.Coordinates.DyadicNormalizedFamily
import OAI.Geometry.RCD.Coordinates.ScaledCoordinates

namespace OAI

/-! # Metric approximation in the exact dyadic normalizing frame -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

/-- The half-ball output of almost splitting covers four radial testing
radii after changing the physical unit by eight. -/
theorem IsPointedApproximation.rescale_eight {X : Type*} [MetricSpace X] {n : ℕ}
    {p : X} {r ε : ℝ} (hr : 0 < r) {f : X → Euclidean n}
    (hf : IsPointedApproximation p 0 (8 * r) (1 / 2) ε f) :
    IsPointedApproximation p 0 r 4 (8 * ε) (fun x => (8 : ℝ) • f x) := by
  have hdist (v w : Euclidean n) : dist ((8 : ℝ) • v) ((8 : ℝ) • w) = 8 * dist v w := by
    rw [dist_smul₀]
    norm_num
  have hrad : (1 / 2 : ℝ) * (8 * r) = 4 * r := by ring
  refine ⟨?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hf.1 (by norm_num : (0 : ℝ) ≤ 8)
    simpa only [← hdist, smul_zero] using h
  · intro x y hx hy
    have h := mul_le_mul_of_nonneg_left (hf.2.1 x y (by rwa [hrad]) (by rwa [hrad]))
      (by norm_num : (0 : ℝ) ≤ 8)
    have h' : |(8 : ℝ) * (dist (f x) (f y) - dist x y / (8 * r))| ≤ 8 * ε := by
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)] using h
    have he : (8 : ℝ) * (dist (f x) (f y) - dist x y / (8 * r)) =
        dist ((8 : ℝ) • f x) ((8 : ℝ) • f y) - dist x y / r := by
      rw [hdist]
      field_simp
    rwa [he] at h'
  · intro y hy
    have hy' : dist ((1 / 8 : ℝ) • y) 0 ≤ 1 / 2 - ε := by
      rw [dist_zero_right, norm_smul]
      norm_num
      have h := hy
      rw [dist_zero_right] at h
      linarith
    obtain ⟨x, hx, hxy⟩ := hf.2.2 ((1 / 8 : ℝ) • y) hy'
    refine ⟨x, by rwa [hrad] at hx, ?_⟩
    have h := mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 8)
    rw [← hdist, smul_smul] at h
    norm_num at h
    exact h

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Choose each dyadic frame once, retaining its exact mean, splitting
data and metric approximation together. The testing radius is 1/128 of
the mean-normalization radius, or 1/64 of the distance-source radius. -/
theorem exists_metric_dyadic_normalized_family (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (p : X) {R T β ρ : ℝ} (hR : 0 < R) (hRT : 4 * R ≤ T)
    (hfamily : ∀ r : ℝ, 0 < r → 64 * r ≤ T →
      ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
          (ball p (16 * r)) measurableSet_ball A ∧
        FirstOrderSplittingOn μ hQ p (16 * r) β (transformedColumn μ hQ u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsPointedApproximation p 0 r (1 / 2) ρ (fun x => r⁻¹ •
          ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
            (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)))) :
    ∃ S : ℕ → Euclidean n ≃L[ℝ] Euclidean n,
      (∀ i, IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
        (ball p (R / 2 ^ i)) measurableSet_ball (S i)) ∧
      (∀ i, FirstOrderSplittingOn μ hQ p (R / 2 ^ i) β (transformedColumn μ hQ u (S i))
        (fun x => (S i : Euclidean n →L[ℝ] Euclidean n).adjoint (v x))) ∧
      ∀ i, IsPointedApproximation p 0 ((R / 2 ^ i) / 128) 4 (8 * ρ)
        (fun x => ((R / 2 ^ i) / 128)⁻¹ •
          ((S i : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
            (S i : Euclidean n →L[ℝ] Euclidean n).adjoint (v p))) := by
  have hchoose (i : ℕ) : ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
        (ball p (R / 2 ^ i)) measurableSet_ball A ∧
      FirstOrderSplittingOn μ hQ p (R / 2 ^ i) β (transformedColumn μ hQ u A)
        (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
      IsPointedApproximation p 0 ((R / 2 ^ i) / 128) 4 (8 * ρ)
        (fun x => ((R / 2 ^ i) / 128)⁻¹ •
          ((A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
            (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v p))) := by
    let d := R / (2 : ℝ) ^ i
    have hd : 0 < d := div_pos hR (by positivity)
    have hdR : d ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    obtain ⟨A, hA, hfirst, happ⟩ := hfamily (d / 16) (by positivity) (by linarith)
    refine ⟨A, by simpa only [show 16 * (d / 16) = d by ring] using hA,
      by simpa only [show 16 * (d / 16) = d by ring] using hfirst, ?_⟩
    have he : d / 16 = 8 * (d / 128) := by ring
    rw [he] at happ
    have hs := happ.rescale_eight (by positivity : 0 < d / 128)
    have hscale : (8 : ℝ) * (8 * (d / 128))⁻¹ = (d / 128)⁻¹ := by
      field_simp
    simpa only [smul_smul, hscale] using hs
  choose S hS using hchoose
  exact ⟨S, fun i => (hS i).1, fun i => (hS i).2.1, fun i => (hS i).2.2⟩

end RegularPointCoordinates

end

end OAI

import OAI.Geometry.RCD.Metric.MeasuredApproximation

namespace OAI

/-! # Bounded Lipschitz tests at arbitrary fixed scale -/

open Set Metric MeasureTheory Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem IsMeasuredEuclideanApproximation.test_bound {μ : Measure X} {n : ℕ}
    {p : X} {r R ε : ℝ} {f : X → Euclidean n}
    (h : IsMeasuredEuclideanApproximation μ n p r R ε f)
    {C : ℝ≥0} (hC : 0 < C) {φ : Euclidean n → ℝ}
    (hφ : LipschitzWith C φ) (hb : ∀ z, |φ z| ≤ C) :
    |(μ.real (ball p (R*r)))⁻¹*(∫ x in ball p (R*r), φ (f x) ∂μ)-
      (volume.real (ball (0 : Euclidean n) R))⁻¹*(∫ z in ball 0 R, φ z)| ≤ C*ε := by
  have hCr : (0:ℝ)<C := hC
  let ψ := fun z => (C:ℝ)⁻¹*φ z
  have hψ : LipschitzWith 1 ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |ψ x-ψ y| ≤ (1:ℝ)*dist x y
    dsimp only [ψ]
    rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hCr)]
    have hh := mul_le_mul_of_nonneg_left (hφ.dist_le_mul x y) (inv_nonneg.mpr hCr.le)
    simpa only [Real.dist_eq,← mul_assoc,inv_mul_cancel₀ hCr.ne',one_mul,NNReal.coe_one] using hh
  have hψb (z : Euclidean n) : |ψ z| ≤ 1 := by
    dsimp only [ψ]
    rw [abs_mul,abs_of_pos (inv_pos.mpr hCr)]
    calc (C:ℝ)⁻¹*|φ z| ≤ (C:ℝ)⁻¹*C := mul_le_mul_of_nonneg_left (hb z) (inv_nonneg.mpr hCr.le)
      _ = 1 := inv_mul_cancel₀ hCr.ne'
  have hh := h.measure_test ψ hψ hψb
  have he : (μ.real (ball p (R*r)))⁻¹*(∫ x in ball p (R*r), ψ (f x) ∂μ)-
      (volume.real (ball (0 : Euclidean n) R))⁻¹*(∫ z in ball 0 R, ψ z) =
      (C:ℝ)⁻¹*((μ.real (ball p (R*r)))⁻¹*(∫ x in ball p (R*r), φ (f x) ∂μ)-
        (volume.real (ball (0 : Euclidean n) R))⁻¹*(∫ z in ball 0 R, φ z)) := by
    simp only [ψ,integral_const_mul]
    ring
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hCr)] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hCr.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hCr.ne',one_mul] using hh'

omit [BorelSpace X] in
theorem measured_approximation_test_tendsto {μ : Measure X} {n : ℕ}
    {p : ℕ → X} {r ε : ℕ → ℝ} {R : ℝ} {f : ℕ → X → Euclidean n}
    (h : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) R (ε k) (f k))
    (hε : Tendsto ε atTop (𝓝 0))
    {C : ℝ≥0} (hC : 0<C) {φ : Euclidean n → ℝ}
    (hφ : LipschitzWith C φ) (hb : ∀ z, |φ z| ≤ C) :
    Tendsto (fun k => (μ.real (ball (p k) (R*r k)))⁻¹*
      (∫ x in ball (p k) (R*r k), φ (f k x) ∂μ)) atTop
      (𝓝 ((volume.real (ball (0 : Euclidean n) R))⁻¹*(∫ z in ball 0 R, φ z))) := by
  apply tendsto_of_tendsto_of_dist tendsto_const_nhds
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun k => by simpa only [Real.dist_eq,abs_sub_comm] using (h k).test_bound hC hφ hb)
  simpa only [mul_zero] using hε.const_mul (C:ℝ)

end RegularPointCoordinates

end

end OAI

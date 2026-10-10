import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds
import OAI.Geometry.RCD.Sobolev.MeasuredTestScaling

namespace OAI

/-! # Scalar and coordinate test limits from measured approximation -/

open Set Metric Filter MeasureTheory
open scoped NNReal Topology ContDiff
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem measured_smooth_test_tendsto {n : ℕ} {S : ℝ} (hS : 0<S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hε : Tendsto ε atTop (𝓝 0)) {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), ψ (v k x) ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 S, ψ z)) := by
  obtain ⟨_,_,_,M,B,hM,hB,_⟩ := hψ.metric_bounds hS
  let C : ℝ≥0 := M+B+1
  have hMC : M≤C := (le_add_of_nonneg_right (show (0:ℝ≥0)≤B from zero_le)).trans
    (le_add_of_nonneg_right zero_le_one)
  have hBC : B≤C := (le_add_of_nonneg_left (show (0:ℝ≥0)≤M from zero_le)).trans
    (le_add_of_nonneg_right zero_le_one)
  exact measured_approximation_test_tendsto hv hε (by dsimp only [C]; positivity)
    (hM.weaken hMC) (fun z => (hB z).trans (by exact_mod_cast hBC))

theorem InteriorSmoothTest.mul_coordinate {n : ℕ} {S : ℝ}
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) (j : Fin n) :
    InteriorSmoothTest n S (fun z => ψ z*z j) := by
  have hj : ContDiff ℝ ∞ (fun z : Euclidean n => z j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) j).contDiff
  refine ⟨hψ.1.mul hj,?_,?_⟩
  · exact hψ.2.1.mul_right
  · exact tsupport_mul_subset_left.trans hψ.2.2

theorem measured_smooth_coordinate_test_tendsto {n : ℕ} {S : ℝ} (hS : 0<S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hε : Tendsto ε atTop (𝓝 0)) {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ)
    (j : Fin n) :
    Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), ψ (v k x)*v k x j ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*∫ z in ball 0 S, ψ z*z j)) :=
  measured_smooth_test_tendsto hS hv hε (hψ.mul_coordinate j)

end RegularPointCoordinates

end

end OAI

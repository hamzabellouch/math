import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightTests
import OAI.Analysis.IrrationalRotation.Sampling.TestedSamplingMoments

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.ProductModel.SamplingWeights
open ScalarSampling

theorem testedCoordinateWeight_first_eq_scalar (I : Finset ℕ) (m i : ℕ)
    (E F : Set ℝ) {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    testedCoordinateWeight false I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i E F s t =
      if i ∈ I then TestedTriangular.firstKernel E F s t
      else TestedSampling.firstKernel m E F s t := by
  by_cases hi : i ∈ I
  · simp [testedCoordinateWeight, coordinateWeight, TestedTriangular.firstKernel, hi]
  · simp [testedCoordinateWeight, coordinateWeight, TestedSampling.firstKernel,
      manuscriptKernel, ScalarSampling.circleKernel, Int.fract_eq_self.mpr hs,
      Int.fract_eq_self.mpr ht, hi]

theorem testedCoordinateWeight_second_eq_scalar (I : Finset ℕ) (m i : ℕ)
    (E F : Set ℝ) (s : ℝ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    testedCoordinateWeight true I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i E F s t =
      if i ∈ I then TestedTriangular.secondKernel E F s t
      else TestedSampling.secondKernel m E F s t := by
  by_cases hi : i ∈ I
  · simp [testedCoordinateWeight, coordinateWeight, TestedTriangular.secondKernel, hi]
  · simp [testedCoordinateWeight, coordinateWeight, TestedSampling.secondKernel,
      manuscriptEndpointKernel, manuscriptKernel, ScalarSampling.circleKernel,
      Int.fract_eq_self.mpr ht, hi]

theorem testedCoordinateWeight_eq_scalar_on_orbit (endpoint : Bool)
    (I : Finset ℕ) (m i n : ℕ) (E F : Set ℝ) (θ : ℕ → ℝ) (x : Base) :
    testedCoordinateWeight endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i E F (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) =
    if endpoint then
      if i ∈ I then TestedTriangular.secondKernel E F
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))
      else TestedSampling.secondKernel m E F
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))
    else
      if i ∈ I then TestedTriangular.firstKernel E F
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i))
      else TestedSampling.firstKernel m E F
        (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
  have ht : Int.fract ((n : ℝ) * θ i) ∈ Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  cases endpoint
  · exact testedCoordinateWeight_first_eq_scalar I m i E F
      (ProductCocycle.representative_mem_Ico (x i)) ht
  · exact testedCoordinateWeight_second_eq_scalar I m i E F _ ht

end Invariant233.ProductModel.SamplingWeights

end

end OAI

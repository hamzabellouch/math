import Mathlib
import OAI.Probability.Perceptron.Variational.CouplingDerivative
import OAI.Probability.Perceptron.Sphere.CoordinateBoxBound

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma perturbationAmplitude_one_mul (N : ℕ) (u : Fin N → ℝ) (j : Fin N) :
    perturbationAmplitude N u j=perturbationAmplitude N (fun _ => 1) j*u j := by
  simp only [perturbationAmplitude,mul_one]

lemma perturbation_normalized_square_sum (n : ℕ) :
    (∑ j : Fin (n+1), 4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ)) ≤
      4*perturbationScale (n+1)^2 := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  have he (j : Fin (n+1)) :
      4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ) =
        4*perturbationScale (n+1)^2*((1/2:ℝ)^(j.val+1))^2 := by
    simp only [perturbationAmplitude,mul_one,perturbationWeight_eq,mul_pow,Real.sq_sqrt hn.le]
    field_simp
  calc
    _ = ∑ j : Fin (n+1), 4*perturbationScale (n+1)^2*((1/2:ℝ)^(j.val+1))^2 := Finset.sum_congr rfl fun j _ => he j
    _ ≤ ∑ j : Fin (n+1), 4*perturbationScale (n+1)^2*(1/2:ℝ)^(j.val+1) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hw0 : (0:ℝ) ≤ (1/2:ℝ)^(j.val+1) := by positivity
      have hw1 : (1/2:ℝ)^(j.val+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    _ = 4*perturbationScale (n+1)^2 * ∑ j : Fin (n+1), (1/2:ℝ)^(j.val+1) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left (half_power_sum_le_one (n+1))
        (show 0 ≤ 4*perturbationScale (n+1)^2 from by positivity)

lemma sourceExpectedPressure_box_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {u v : Fin (n+1) → ℝ} (hu : ∀ j, u j ∈ Icc 0 2) (hv : ∀ j, v j ∈ Icc 0 2) :
    |(∫ a, sourceKernelPressure n k f p d v h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw))-
      ∫ a, sourceKernelPressure n k f p d u h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)| ≤
      ∑ j : Fin (n+1), (4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ))*|v j-u j| := by
  apply box_sum_coordinate_comparison (a := (0:ℝ)) (b := (2:ℝ)) (hu := hu) (hv := hv)
  intro w hw j
  obtain ⟨D,hD,hDb⟩ := sourceExpectedPressure_coordinate_derivative_bound n k f p d h hh0 hh w j z hz hz0 hz1 t
  refine ⟨D,hD,hDb.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [perturbationAmplitude_one_mul (n+1) w j]
  rw [← mul_assoc,← pow_two,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (hw j).1]
  nlinarith [mul_le_mul_of_nonneg_left (hw j).2 (sq_nonneg (perturbationAmplitude (n+1) (fun _ => 1) j))]

lemma sourceExpectedPressure_perturbation_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {u v : Fin (n+1) → ℝ} (hu : ∀ j, u j ∈ Icc 0 2) (hv : ∀ j, v j ∈ Icc 0 2) :
    |(∫ a, sourceKernelPressure n k f p d v h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw))-
      ∫ a, sourceKernelPressure n k f p d u h a ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw)| ≤
      8*perturbationScale (n+1)^2 := by
  apply (sourceExpectedPressure_box_comparison n k f p d h hh0 hh z hz hz0 hz1 t hu hv).trans
  calc
    _ ≤ ∑ j : Fin (n+1), (4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ))*2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact abs_le.mpr ⟨by linarith [(hu j).2,(hv j).1],by linarith [(hu j).1,(hv j).2]⟩
    _ = 2*∑ j : Fin (n+1), 4*perturbationAmplitude (n+1) (fun _ => 1) j^2/(n+1:ℕ) := by rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ _ := by nlinarith [perturbation_normalized_square_sum n]

end SphericalPerceptronFreeEnergy
end

end OAI

import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianBoltzmann

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma countableGaussianField_update (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (i : ℕ) (t : ℝ) (x : S) :
    countableGaussianField v L (Function.update g i t) x =
      countableGaussianField v L (Function.update g i 0) x+t*maskedGaussianCoefficient v L i x := by
  unfold countableGaussianField gaussianPrefixField
  rw [Fin.sum_univ_eq_sum_range (fun j => Function.update g i t j*v j x) (L x),
    Fin.sum_univ_eq_sum_range (fun j => Function.update g i 0 j*v j x) (L x)]
  have he (j : ℕ) : Function.update g i t j*v j x =
      Function.update g i 0 j*v j x+if j=i then t*v i x else 0 := by
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self,ite_true,zero_mul,zero_add]
    · simp only [Function.update_of_ne hj,ite_eq_right hj,add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range,maskedGaussianCoefficient]
  split_ifs <;> simp

omit [MeasurableSpace S] in
lemma countableGaussianHamiltonian_update (W : S → ℝ) (v : ℕ → S → ℝ) (L : S → ℕ)
    (g : ℕ → ℝ) (i : ℕ) (t : ℝ) (x : S) :
    countableGaussianHamiltonian W v L (Function.update g i t) x =
      countableGaussianHamiltonian W v L (Function.update g i 0) x+t*maskedGaussianCoefficient v L i x := by
  unfold countableGaussianHamiltonian
  conv_lhs => rw [countableGaussianField_update]
  ring

omit [MeasurableSpace S] in
lemma maskedGaussianCoefficient_bound (v : ℕ → S → ℝ) (L : S → ℕ)
    {D : ℝ} (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D) (i : ℕ) (x : S) :
    |maskedGaussianCoefficient v L i x| ≤ Real.sqrt D := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · apply Real.abs_le_sqrt
    exact (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (v j.val x))
      (Finset.mem_univ (⟨i,hi⟩ : Fin (L x)))).trans (hD x)
  · simpa only [abs_zero] using Real.sqrt_nonneg D

end SphericalPerceptronFreeEnergy
end

end OAI

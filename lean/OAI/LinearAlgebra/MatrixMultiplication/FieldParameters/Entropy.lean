import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Weights
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

def homogeneousEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  (∑ a, p a) * Real.log (∑ a, p a) + finiteEntropy p

theorem homogeneousEntropy_normalized {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a = 1) :
    homogeneousEntropy p = finiteEntropy p := by
  simp [homogeneousEntropy, hp]

theorem entropyTerm_divide (x m : ℝ) :
    entropyTerm (x / m) = entropyTerm x / m + (x / m) * Real.log m := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hm : m = 0
  · simp [hm]
  rw [entropyTerm, Real.log_div hx hm]
  unfold entropyTerm
  ring

theorem homogeneousEntropy_eq_mass_mul {A : Type*} [Fintype A]
    (p : A → ℝ) (hm : ∑ a, p a ≠ 0) :
    homogeneousEntropy p =
      (∑ a, p a) * finiteEntropy (fun a => p a / ∑ b, p b) := by
  simp only [finiteEntropy, entropyTerm_divide, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_mul]
  unfold homogeneousEntropy finiteEntropy
  rw [div_self hm]
  field_simp
  ring

theorem homogeneousEntropy_zero {A : Type*} [Fintype A] :
    homogeneousEntropy (fun _ : A => 0) = 0 := by
  simp [homogeneousEntropy, finiteEntropy]

theorem homogeneousEntropy_expansion {A : Type*} [Fintype A] (p : A → ℝ) :
    homogeneousEntropy p =
      (∑ a, p a) * Real.log (∑ a, p a) - ∑ a, p a * Real.log (p a) := by
  simp only [homogeneousEntropy, finiteEntropy, entropyTerm, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end

end MatrixMultiplication.AllFieldParameters

end OAI

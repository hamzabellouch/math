import OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison

namespace OAI

noncomputable section
namespace PiExponent.WeightedCurveRigidity

open scoped BigOperators
open PiExponentApprox PersistentWeightComparison

theorem logarithmic_coordinate_eq_one {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ sigma * N → polynomialFrameWord m word F ∈ P)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ))
    (a : Fin (m + 1) → ℂ) (ha : a 0 = 1)
    (hcenter : ∀ p ∈ P, MvPolynomial.eval a p = 0) :
    MvPolynomial.X (0 : Fin (m + 1)) - 1 ∈ P := by
  apply CurveComponentRigidity.coordinate_eq_one_of_persistent_comparison
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ) + 2)) * N) (fun i => (hcost i).le) (by positivity)
    F hF0 P hP hheight hY _
    (logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma hN hrect F hF P hY)
    hseparated a ha hcenter
  intro word hword
  apply hvanish word
  have hm : (m : ℝ) + 2 ≠ 0 := by positivity
  have heq : ((m : ℝ) + 2) * ((sigma / ((m : ℝ) + 2)) * N) = sigma * N := by
    field_simp
  simpa only [heq] using hword

theorem ordinary_coordinate_constant {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n) (hF0 : F ≠ 0)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (d : ℕ) (hd : d ≤ m)
    (P : Ideal (OrdinaryDerivatives.Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ word : List (Fin n), DerivativeIdeals.wordCost cost word ≤ sigma * N →
      OrdinaryDerivatives.word n word F ∈ P)
    (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    ∃ i : Fin n, ∃ c : ℂ, MvPolynomial.X i - MvPolynomial.C c ∈ P := by
  apply OrdinaryComponentRigidity.coordinate_constant_of_persistent_comparison
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ) + 2)) * N) (fun i => (hcost i).le) (by positivity)
    F hF0 d P hP hheight _
    (ordinary_persistent_comparison hn rho hrho cost hcost sigma N hsigma hN hrect F hF d P)
    hseparated
  intro word hword
  apply hvanish word
  have hdR : (d : ℝ) ≤ m := by exact_mod_cast hd
  have hm : (m : ℝ) + 2 ≠ 0 := by positivity
  have heq : ((m : ℝ) + 2) * ((sigma / ((m : ℝ) + 2)) * N) = sigma * N := by
    field_simp
  apply hword.trans
  rw [← heq]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem ordinary_at_most_one_center {m n : ℕ} (hn : n ≤ m + 2)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ) + 2)) N)
    (F : OrdinaryDerivatives.Polynomial n) (hF0 : F ≠ 0)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (d : ℕ) (hd : d ≤ m)
    (P : Ideal (OrdinaryDerivatives.Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ word : List (Fin n), DerivativeIdeals.wordCost cost word ≤ sigma * N →
      OrdinaryDerivatives.word n word F ∈ P)
    (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ))
    {J : Type*} (a : J → Fin n → ℂ) (ha : ∀ i, Function.Injective (fun j => a j i))
    (j l : J) (hj : ∀ p ∈ P, MvPolynomial.eval (a j) p = 0)
    (hl : ∀ p ∈ P, MvPolynomial.eval (a l) p = 0) : j = l := by
  obtain ⟨i, c, hc⟩ := ordinary_coordinate_constant hn rho hrho cost hcost sigma N hsigma
    hN hrect F hF0 hF d hd P hP hheight hvanish hseparated
  have hjc := hj _ hc
  have hlc := hl _ hc
  simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] at hjc hlc
  exact ha i (hjc.trans hlc.symm)

end PiExponent.WeightedCurveRigidity
end

end OAI

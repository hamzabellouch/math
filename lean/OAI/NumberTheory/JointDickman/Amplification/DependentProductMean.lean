import OAI.NumberTheory.JointDickman.Counting.SamplingMoments
import OAI.NumberTheory.JointDickman.Amplification.ProductComparison

namespace OAI

/-! # Coordinate means for the prime-dependent higher-digit spaces -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem finiteProduct_expectation_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p f : ∀ i, Ω i → ℝ) :
    finiteExpectation (finiteProductMass p) (fun x => ∏ i, f i (x i)) =
      ∏ i, finiteExpectation (p i) (f i) := by
  simp only [finiteExpectation,finiteProductMass,← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => p i x*f i x)).symm

theorem finiteProduct_expectation_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i, ∑ x, p i x = 1)
    (i : ι) (f : Ω i → ℝ) :
    finiteExpectation (finiteProductMass p) (fun x => f (x i)) =
      finiteExpectation (p i) f := by
  let g : ∀ j, Ω j → ℝ := fun j x => if h : j = i then f (h ▸ x) else 1
  have hl (x : ∀ j, Ω j) : (∏ j, g j (x j)) = f (x i) := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji; simp [g,hji]
    · simp
  have hr : (∏ j, finiteExpectation (p j) (g j)) = finiteExpectation (p i) f := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji; simp [g,hji,finiteExpectation,hp]
    · simp
  simpa only [hl,hr] using finiteProduct_expectation_prod p g

end JointDickman

end OAI

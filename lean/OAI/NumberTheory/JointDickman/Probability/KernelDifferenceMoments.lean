import OAI.NumberTheory.JointDickman.Counting.SamplingMoments

namespace OAI

/-! # Row-moment bounds for the error between two finite kernels -/
namespace JointDickman
open Finset PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteRowMean_add (p : ι → A → ℝ) (K J : ι → ι → A → A → ℝ)
    (i : ι) (a : A) :
    siteRowMean p (fun i j a b => K i j a b+J i j a b) i a =
      siteRowMean p K i a+siteRowMean p J i a := by
  simp only [siteRowMean,finiteExpectation_add,sum_add_distrib]

theorem siteRowSquareMass_add_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (K J : ι → ι → A → A → ℝ) (i : ι) :
    siteRowSquareMass p (fun i j a b => K i j a b+J i j a b) i ≤
      2*siteRowSquareMass p K i+2*siteRowSquareMass p J i := by
  unfold siteRowSquareMass
  calc
    _ ≤ finiteExpectation (p i) (fun a => ∑ j : {j : ι // j ≠ i},
        finiteExpectation (p j) (fun b => 2*(K i j a b)^2+2*(J i j a b)^2)) := by
      apply finiteExpectation_mono (p i) (hp i)
      intro a
      apply sum_le_sum
      intro j _
      apply finiteExpectation_mono (p j) (hp j)
      intro b
      nlinarith [sq_nonneg (K i j a b-J i j a b)]
    _ = _ := by
      simp only [finiteExpectation_add,finiteExpectation_const_mul,sum_add_distrib,← mul_sum]

theorem siteRowSquareMass_sub_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (K J : ι → ι → A → A → ℝ) (i : ι) :
    siteRowSquareMass p (fun i j a b => K i j a b-J i j a b) i ≤
      2*siteRowSquareMass p K i+2*siteRowSquareMass p J i := by
  unfold siteRowSquareMass
  calc
    _ ≤ finiteExpectation (p i) (fun a => ∑ j : {j : ι // j ≠ i},
        finiteExpectation (p j) (fun b => 2*(K i j a b)^2+2*(J i j a b)^2)) := by
      apply finiteExpectation_mono (p i) (hp i)
      intro a
      apply sum_le_sum
      intro j _
      apply finiteExpectation_mono (p j) (hp j)
      intro b
      nlinarith [sq_nonneg (K i j a b+J i j a b)]
    _ = _ := by
      simp only [finiteExpectation_add,finiteExpectation_const_mul,sum_add_distrib,← mul_sum]

end JointDickman

end OAI

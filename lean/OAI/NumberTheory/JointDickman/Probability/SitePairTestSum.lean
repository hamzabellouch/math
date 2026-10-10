import OAI.NumberTheory.JointDickman.Probability.SiteTestRestriction

namespace OAI

/-! # Summing the two-endpoint tests needed by sampling -/
namespace JointDickman
open Finset PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteTestMean_le_pair_sum (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (E : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, E i i a a = 0) (r : ι → ι → ℝ) (hrdiag : ∀ i, 0 ≤ r i i)
    (hpair : ∀ i j, i ≠ j → ∀ g h : A → ℝ,
      (∀ a, |g a| ≤ 1) → (∀ b, |h b| ≤ 1) →
      finiteExpectation (p i) (fun a => finiteExpectation (p j)
        (fun b => E i j a b*g a*h b)) ≤ r i j)
    (g h : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean p E g h ≤ ∑ i, ∑ j, r i j := by
  unfold siteTestMean
  rw [finiteExpectation_sum]
  apply sum_le_sum
  intro i _
  rw [finiteExpectation_sum]
  apply sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [hdiag,zero_mul,finiteExpectation,mul_zero,sum_const_zero]
    exact hrdiag i
  · exact (siteProduct_expectation_two p hpone hij
      (fun a b => E i j a b*g i a*h j b)).trans_le
      (hpair i j hij (g i) (h j) (hg i) (hh j))

theorem siteTestMean_le_of_pair_rows (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (E : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, E i i a a = 0) (r : ι → ι → ℝ) (hrdiag : ∀ i, 0 ≤ r i i)
    (hpair : ∀ i j, i ≠ j → ∀ g h : A → ℝ,
      (∀ a, |g a| ≤ 1) → (∀ b, |h b| ≤ 1) →
      finiteExpectation (p i) (fun a => finiteExpectation (p j)
        (fun b => E i j a b*g a*h b)) ≤ r i j)
    {e : ℝ} (hr : ∀ i, (∑ j, r i j) ≤ e)
    (g h : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e :=
  (siteTestMean_le_pair_sum p hpone E hdiag r hrdiag hpair g h hg hh).trans
    ((sum_le_sum (fun i _ => hr i)).trans_eq (by simp))

end JointDickman

end OAI

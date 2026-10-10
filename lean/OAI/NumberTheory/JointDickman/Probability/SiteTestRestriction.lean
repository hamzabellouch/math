import OAI.NumberTheory.JointDickman.Probability.MaskedSiteMoments

namespace OAI

/-! # Single-site tests after fixing sampled coordinates -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def siteTestMean (p : ι → A → ℝ) (E : ι → ι → A → A → ℝ)
    (g h : ι → A → ℝ) : ℝ :=
  finiteExpectation (siteProductMass p)
    (fun x => ∑ i, ∑ j, E i j (x i) (x j) * g i (x i) * h j (x j))

noncomputable def maskedSiteTest (J : Finset ι) (g : ι → A → ℝ) (i : ι) (a : A) : ℝ :=
  if i ∈ J then 0 else g i a

theorem siteProduct_unfrozen_pair (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (J : Finset ι) (t : ι → A)
    {i j : ι} (hi : i ∉ J) (hj : j ∉ J) (F : A → A → ℝ) :
    finiteExpectation (siteProductMass (frozenSiteMass p J t)) (fun x => F (x i) (x j)) =
      finiteExpectation (siteProductMass p) (fun x => F (x i) (x j)) := by
  by_cases hij : i = j
  · subst j
    rw [siteProduct_expectation_coordinate _ (frozenSiteMass_sum p hpone J t) i (fun a => F a a),
      siteProduct_expectation_coordinate _ hpone i (fun a => F a a)]
    simp only [finiteExpectation,frozenSiteMass,hi,ite_false]
  · rw [siteProduct_expectation_two _ (frozenSiteMass_sum p hpone J t) hij,
      siteProduct_expectation_two _ hpone hij]
    simp only [finiteExpectation,frozenSiteMass,hi,hj,ite_false]

theorem siteTestMean_masked_frozen (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (J : Finset ι) (t : ι → A)
    (E : ι → ι → A → A → ℝ) (g h : ι → A → ℝ) :
    siteTestMean (frozenSiteMass p J t) (maskedSiteKernel J E) g h =
      siteTestMean p E (maskedSiteTest J g) (maskedSiteTest J h) := by
  unfold siteTestMean
  rw [finiteExpectation_sum,finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  rw [finiteExpectation_sum,finiteExpectation_sum]
  apply sum_congr rfl
  intro j _
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · simp [maskedSiteKernel,maskedSiteTest,hi,hj,finiteExpectation]
  · simp [maskedSiteKernel,maskedSiteTest,hi,hj,finiteExpectation]
  · simp [maskedSiteKernel,maskedSiteTest,hi,hj,finiteExpectation]
  · simp only [maskedSiteKernel,maskedSiteTest,hi,hj,not_false_eq_true,and_self,
      ite_true,ite_false]
    exact siteProduct_unfrozen_pair p hpone J t hi hj (fun a b => E i j a b*g i a*h j b)

theorem siteTestMean_restriction_bound (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (E : ι → ι → A → A → ℝ) (C : ℝ)
    (htest : ∀ g h : ι → A → ℝ, (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
      siteTestMean p E g h ≤ C)
    (J : Finset ι) (t : ι → A) (g h : ι → A → ℝ)
    (hg : ∀ i a, |g i a| ≤ 1) (hh : ∀ i a, |h i a| ≤ 1) :
    siteTestMean (frozenSiteMass p J t) (maskedSiteKernel J E) g h ≤ C := by
  rw [siteTestMean_masked_frozen p hpone J t E g h]
  apply htest
  · intro i a
    by_cases hi : i ∈ J <;> simp [maskedSiteTest,hi,hg]
  · intro i a
    by_cases hi : i ∈ J <;> simp [maskedSiteTest,hi,hh]

end JointDickman

end OAI

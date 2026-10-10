import OAI.NumberTheory.JointDickman.Probability.FrozenSiteLaw

namespace OAI

/-! # Deleting the sampled sites preserves the moment bounds -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def maskedSiteKernel (J : Finset ι) (K : ι → ι → A → A → ℝ)
    (i j : ι) (a b : A) : ℝ :=
  if i ∉ J ∧ j ∉ J then K i j a b else 0

omit [Fintype ι] [Fintype A] in
theorem maskedSiteKernel_diag (J : Finset ι) (K : ι → ι → A → A → ℝ)
    (hdiag : ∀ i a, K i i a a = 0) : ∀ i a, maskedSiteKernel J K i i a a = 0 := by
  intro i a
  simp [maskedSiteKernel,hdiag]

theorem maskedSiteKernel_mean_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (J : Finset ι) (t : ι → A) (H : ι → ι → A → A → ℝ)
    (hH : ∀ i j a b, 0 ≤ H i j a b) {C : ℝ} (hC : 0 ≤ C)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C) :
    ∀ i a, |siteRowMean (frozenSiteMass p J t) (maskedSiteKernel J H) i a| ≤ C := by
  intro i a
  by_cases hi : i ∈ J
  · simpa [siteRowMean,maskedSiteKernel,hi,finiteExpectation] using hC
  · have hn : 0 ≤ siteRowMean (frozenSiteMass p J t) (maskedSiteKernel J H) i a := by
      apply sum_nonneg
      intro j _
      apply finiteExpectation_nonneg _ _ (frozenSiteMass_nonneg p hp J t j)
      intro b
      unfold maskedSiteKernel
      split_ifs <;> first | exact hH i j a b | rfl
    rw [abs_of_nonneg hn]
    refine le_trans ?_ ((le_abs_self _).trans (hmean i a))
    apply sum_le_sum
    intro j _
    by_cases hj : (j : ι) ∈ J
    · simp only [maskedSiteKernel,hj,not_true_eq_false,and_false,ite_false]
      simp only [finiteExpectation,mul_zero,sum_const_zero]
      exact finiteExpectation_nonneg _ _ (hp j) (fun b => hH i j a b)
    · simp only [finiteExpectation,frozenSiteMass,maskedSiteKernel,hi,hj,
        not_false_eq_true,and_self,ite_true,ite_false]
      exact le_rfl

theorem maskedSiteKernel_square_le (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (J : Finset ι) (t : ι → A) (K : ι → ι → A → A → ℝ) (i : ι) :
    siteRowSquareMass (frozenSiteMass p J t) (maskedSiteKernel J K) i ≤
      siteRowSquareMass p K i := by
  by_cases hi : i ∈ J
  · simp only [siteRowSquareMass,maskedSiteKernel,hi,not_true_eq_false,false_and,
      ite_false,zero_pow (by decide : 2 ≠ 0),finiteExpectation,mul_zero,sum_const_zero]
    exact sum_nonneg fun a _ => mul_nonneg (hp i a) (sum_nonneg fun j _ =>
      sum_nonneg fun b _ => mul_nonneg (hp j b) (sq_nonneg _))
  · unfold siteRowSquareMass
    have he : frozenSiteMass p J t i = p i := by
      funext a
      simp [frozenSiteMass,hi]
    rw [he]
    apply finiteExpectation_mono (p i) (hp i)
    intro a
    apply sum_le_sum
    intro j _
    by_cases hj : (j : ι) ∈ J
    · simp only [maskedSiteKernel,hj,not_true_eq_false,and_false,ite_false,
        zero_pow (by decide : 2 ≠ 0),finiteExpectation,mul_zero,sum_const_zero]
      exact sum_nonneg fun b _ => mul_nonneg (hp j b) (sq_nonneg _)
    · simp only [finiteExpectation,frozenSiteMass,maskedSiteKernel,hi,hj,
        not_false_eq_true,and_self,ite_true,ite_false]
      exact le_rfl

end JointDickman

end OAI

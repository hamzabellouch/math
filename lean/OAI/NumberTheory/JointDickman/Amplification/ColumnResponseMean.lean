import OAI.NumberTheory.JointDickman.Probability.SiteTestRestriction

namespace OAI

/-! # A fixed single-site comparison bounds the mean column response -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

theorem siteRowSquareMass_mono (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (E F : ι → ι → A → A → ℝ)
    (hEF : ∀ i j a b, (E i j a b)^2 ≤ (F i j a b)^2) (i : ι) :
    siteRowSquareMass p E i ≤ siteRowSquareMass p F i := by
  apply finiteExpectation_mono _ (hp i)
  intro a
  apply sum_le_sum
  intro j _
  exact finiteExpectation_mono _ (hp j) (fun b => hEF i j a b)

theorem siteColumnResponse_mean_le (p : ι → A → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E : ι → ι → A → A → ℝ)
    (hsym : ∀ i j a b, E i j a b = E j i b a)
    (hdiag : ∀ i a, E i i a a = 0)
    (g : ι → A → ℝ) (hg : ∀ i a, |g i a| ≤ 1) (C q : ℝ)
    (htest : ∀ h : ι → A → ℝ, (∀ i a, |h i a| ≤ 1) → siteTestMean p E g h ≤ C)
    (hsquare : ∀ i, siteRowSquareMass p E i ≤ q) :
    finiteExpectation (siteProductMass p) (siteColumnResponse E g) ≤
      C + (Fintype.card ι : ℝ) * Real.sqrt q := by
  let K := fun i j a b => E j i b a * g j b
  have hKd : ∀ i a, K i i a a = 0 := by intro i a; simp [K,hdiag]
  have hKsq : ∀ i, siteRowSquareMass p K i ≤ q := by
    intro i
    refine (siteRowSquareMass_mono p hp K E ?_ i).trans (hsquare i)
    intro k j a b
    have hb : |K k j a b| ≤ |E k j a b| := by
      simp only [K,abs_mul]
      calc
        _ ≤ |E j k b a| * 1 := mul_le_mul_of_nonneg_left (hg j b) (abs_nonneg _)
        _ = _ := by rw [mul_one,hsym j k b a]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hb
  have hKt : ∀ h : ι → A → ℝ, (∀ i a, |h i a| ≤ 1) →
      finiteExpectation (siteProductMass p)
        (fun x => ∑ k, siteRowSum K k x*h k (x k)) ≤ C := by
    intro h hh
    convert htest h hh using 1
    congr 1
    funext x
    simp only [siteRowSum,K,sum_mul]
    rw [sum_comm]
  have hb := siteRow_total_abs_of_tests p hp hpone K hKd C hKt
  change finiteExpectation (siteProductMass p) (siteColumnResponse E g) ≤ _ at hb
  refine hb.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ ∑ _i : ι, Real.sqrt q := sum_le_sum fun i _ => Real.sqrt_le_sqrt (hKsq i)
    _ = _ := by simp

end JointDickman

end OAI

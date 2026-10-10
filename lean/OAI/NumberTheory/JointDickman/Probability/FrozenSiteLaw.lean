import OAI.NumberTheory.JointDickman.Probability.SiteGoodEvent

namespace OAI

/-! # Conditioning on a fixed collection of sampled sites -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Sampled coordinates are fixed; every other coordinate keeps its law. -/
noncomputable def frozenSiteMass (p : ι → A → ℝ) (J : Finset ι) (t : ι → A)
    (i : ι) (a : A) : ℝ :=
  if i ∈ J then if a = t i then 1 else 0 else p i a

omit [Fintype ι] [Fintype A] in
theorem frozenSiteMass_nonneg (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (J : Finset ι) (t : ι → A) : ∀ i a, 0 ≤ frozenSiteMass p J t i a := by
  intro i a
  unfold frozenSiteMass
  split_ifs <;> first | positivity | exact hp i a

omit [Fintype ι] in
theorem frozenSiteMass_sum (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (J : Finset ι) (t : ι → A) : ∀ i, ∑ a, frozenSiteMass p J t i a = 1 := by
  intro i
  by_cases hi : i ∈ J <;> simp [frozenSiteMass,hi,hpone]

theorem frozenSiteMass_average (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (J : Finset ι) (x : ι → A) :
    (∑ t, siteProductMass p t * siteProductMass (frozenSiteMass p J t) x) =
      siteProductMass p x := by
  simp only [siteProductMass,← prod_mul_distrib]
  unfold frozenSiteMass
  rw [← Fintype.prod_sum (fun i a => p i a *
    (if i ∈ J then if x i = a then 1 else 0 else p i (x i)))]
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ J
  · simp [hi]
  · simp [hi,← sum_mul,hpone]

omit [Fintype A] in
theorem frozenSiteMass_support (p : ι → A → ℝ) (J : Finset ι) (t x : ι → A)
    (hx : siteProductMass (frozenSiteMass p J t) x ≠ 0) :
    ∀ i ∈ J, x i = t i := by
  intro i hi
  have hn : frozenSiteMass p J t i (x i) ≠ 0 :=
    (prod_ne_zero_iff.mp hx) i (mem_univ i)
  by_contra hne
  exact hn (by simp [frozenSiteMass,hi,hne])

/-- Averaging the conditional law recovers the original law. The test may
depend on the fixed types, provided only their sampled coordinates matter. -/
theorem frozenSiteMass_disintegrate (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (J : Finset ι)
    (F : (ι → A) → (ι → A) → ℝ)
    (hF : ∀ t x, (∀ i ∈ J, x i = t i) → F t x = F x x) :
    finiteExpectation (siteProductMass p) (fun x => F x x) =
      finiteExpectation (siteProductMass p) (fun t =>
        finiteExpectation (siteProductMass (frozenSiteMass p J t)) (F t)) := by
  unfold finiteExpectation
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  symm
  calc
    _ = ∑ t, (siteProductMass p t * siteProductMass (frozenSiteMass p J t) x) * F x x := by
      apply sum_congr rfl
      intro t _
      by_cases hx : siteProductMass (frozenSiteMass p J t) x = 0
      · simp [hx]
      · rw [hF t x (frozenSiteMass_support p J t x hx)]
        ring
    _ = _ := by rw [← sum_mul,frozenSiteMass_average p hpone]

end JointDickman

end OAI

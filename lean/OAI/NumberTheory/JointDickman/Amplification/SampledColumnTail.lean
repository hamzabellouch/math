import OAI.NumberTheory.JointDickman.Probability.SampledSiteResponse

namespace OAI

/-! # Uniform tails for the finite family of column samples -/

namespace JointDickman
open Finset Classical PublishedInputs

theorem finiteProbability_eq_expectation {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (P : Ω → Prop) :
    finiteProbability w P = finiteExpectation w (fun x => if P x then 1 else 0) := by
  unfold finiteProbability finiteExpectation
  apply sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype A] [DecidableEq A]

theorem sampledColumn_tail (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j a b, E i j a b = E j i b a)
    (hHsym : ∀ i j a b, H i j a b = H j i b a)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    {C q d e L u a : ℝ} (hC : 0 ≤ C) (hd : 0 < d) (hgap : C < d)
    (hL : 0 ≤ L) (ha : 0 < a)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q)
    (htest : ∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e)
    (hbad : (Fintype.card ι : ℝ)*q/(d-C)^2 < 1)
    (hbound : e + Real.sqrt q + L*((Fintype.card ι : ℝ)*q/(d-C)^2) ≤ u)
    (hcut : u+a < L) {m : ℕ} (s : ColumnSample (ι := ι) m) :
    finiteProbability (siteProductMass p)
      (fun x => (∀ i, siteRowSum H i x ≤ d) ∧
        u+a < columnSampleNorm (realizedSiteKernel E x) s) ≤
      Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
  let J : Finset ι := univ.image s.1
  let R := maskedSiteKernel J E
  let V := maskedSiteKernel J H
  let Z := fun t x => siteColumnResponse R (sampledSiteTest E s t) x/Fintype.card ι
  have hH : ∀ i j b c, 0 ≤ H i j b c := fun i j b c => (abs_nonneg _).trans (hdom i j b c)
  have hR : ∀ i j b c, R i j b c = R j i c b := by
    intro i j b c
    simp only [R,maskedSiteKernel]
    simp only [and_comm]
    rw [hEsym]
  have hV : ∀ i j b c, V i j b c = V j i c b := by
    intro i j b c
    simp only [V,maskedSiteKernel]
    simp only [and_comm]
    rw [hHsym]
  have hRV : ∀ i j b c, |R i j b c| ≤ V i j b c := by
    intro i j b c
    dsimp only [R,V,maskedSiteKernel]
    split_ifs <;> first | exact hdom i j b c | simp
  have htail (t : ι → A) :
      finiteProbability (siteProductMass (frozenSiteMass p J t))
        (fun x => (∀ i, siteRowSum H i x ≤ d) ∧ u+a < Z t x) ≤
        Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hh := siteColumnResponse_concentration hMC (frozenSiteMass p J t)
      (frozenSiteMass_nonneg p hp J t) (frozenSiteMass_sum p hpone J t) R V hR hV
      (maskedSiteKernel_diag J E hEdiag) (maskedSiteKernel_diag J H hHdiag) hRV
      (sampledSiteTest E s t) (sampledSiteTest_bound E s t) hd hgap hL ha
      (maskedSiteKernel_mean_le p hp J t H hH hC hmean)
      (fun i => (maskedSiteKernel_square_le p hp J t H i).trans (hsquareH i))
      (fun i => (maskedSiteKernel_square_le p hp J t E i).trans (hsquareE i))
      (fun h hh => siteTestMean_restriction_bound p hpone E _ htest J t _ h
        (sampledSiteTest_bound E s t) hh) hbad
      (by simpa only [mul_div_cancel_left₀ _ hn] using hbound) hcut
    refine (finiteProbability_mono _
      (siteProductMass_nonneg _ (frozenSiteMass_nonneg p hp J t)) ?_).trans hh
    intro x hx
    exact ⟨fun i => (maskedSiteKernel_row_le H hH J x i).trans (hx.1 i),hx.2⟩
  let F : (ι → A) → (ι → A) → ℝ := fun t x =>
    if (∀ i, siteRowSum H i x ≤ d) ∧ u+a < Z t x then 1 else 0
  have hF : ∀ t x, (∀ i ∈ J, x i = t i) → F t x = F x x := by
    intro t x hx
    have he := sampledSiteTest_agree E s t x hx
    simp only [F,Z,he]
  have hid := frozenSiteMass_disintegrate p hpone J F hF
  rw [finiteProbability_eq_expectation]
  have hz (x : ι → A) : columnSampleNorm (realizedSiteKernel E x) s = Z x x :=
    columnSampleNorm_eq_response E s x
  simp only [hz]
  change finiteExpectation (siteProductMass p) (fun x => F x x) ≤ _
  rw [hid]
  calc
    _ ≤ finiteExpectation (siteProductMass p)
        (fun _ => Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2))) := by
      apply finiteExpectation_mono _ (siteProductMass_nonneg p hp)
      intro t
      have hh := htail t
      rw [finiteProbability_eq_expectation] at hh
      convert hh using 1
      unfold finiteExpectation
      apply sum_congr rfl
      intro x _
      by_cases hx : (∀ i, siteRowSum H i x ≤ d) ∧ u+a < Z t x <;> simp [F,hx]
    _ = _ := finiteExpectation_const _ (siteProductMass_sum p hpone) _

end JointDickman

end OAI

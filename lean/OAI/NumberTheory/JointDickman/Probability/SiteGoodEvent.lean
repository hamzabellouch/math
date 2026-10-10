import OAI.NumberTheory.JointDickman.Probability.SiteDegreeTail

namespace OAI

/-! # A single good event for degrees and total square mass -/

namespace JointDickman
open Finset Classical
open PublishedInputs

theorem finiteProbability_or_le {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (E F : Ω → Prop) :
    finiteProbability w (fun x => E x ∨ F x) ≤ finiteProbability w E+finiteProbability w F := by
  unfold finiteProbability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf,hw x]

noncomputable def siteTotalSquare {ι A : Type*} [Fintype ι]
    (K : ι → ι → A → A → ℝ) (x : ι → A) : ℝ :=
  ∑ i, ∑ j, (K i j (x i) (x j))^2

theorem siteTotalSquare_expectation {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0) :
    finiteExpectation (siteProductMass p) (siteTotalSquare K) = ∑ i, siteRowSquareMass p K i := by
  unfold siteTotalSquare
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro i _
  rw [finiteExpectation_sum,siteRowSquareMass_eq_sum_entries p hpone K hdiag i]

theorem siteTotalSquare_bad_probability {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (K : ι → ι → A → A → ℝ) (hdiag : ∀ i a, K i i a a = 0)
    {q Q : ℝ} (hQ : 0 < Q) (hsquare : ∀ i, siteRowSquareMass p K i ≤ q) :
    finiteProbability (siteProductMass p) (fun x => Q < siteTotalSquare K x) ≤
      (Fintype.card ι : ℝ)*q/Q := by
  refine (finiteProbability_markov (siteProductMass p) (siteTotalSquare K)
    (siteProductMass_nonneg p hp) (fun _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) hQ).trans ?_
  rw [siteTotalSquare_expectation p hpone K hdiag]
  exact div_le_div_of_nonneg_right
    ((sum_le_sum (fun i _ => hsquare i)).trans_eq (by simp)) hQ.le

/-- The one common event used before taking a finite union of concentration
tails. Its complement is charged once, not once per column sample. -/
def SiteKernelGood {ι A : Type*} [Fintype ι]
    (E H : ι → ι → A → A → ℝ) (d Q : ℝ) (x : ι → A) : Prop :=
  (∀ i, siteRowSum H i x ≤ d) ∧ siteTotalSquare E x ≤ Q

theorem siteKernelGood_bad_probability {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    {C d q Q : ℝ} (hgap : C < d) (hQ : 0 < Q)
    (hmean : ∀ i a, |siteRowMean p H i a| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q) :
    finiteProbability (siteProductMass p) (fun x => ¬ SiteKernelGood E H d Q x) ≤
      (Fintype.card ι : ℝ)*q/(d-C)^2+(Fintype.card ι : ℝ)*q/Q := by
  have he : (fun x => ¬ SiteKernelGood E H d Q x) =
      (fun x => (¬ ∀ i, siteRowSum H i x ≤ d) ∨ Q < siteTotalSquare E x) := by
    funext x
    simp only [SiteKernelGood,not_and_or,not_le]
  rw [he]
  exact (finiteProbability_or_le _ (siteProductMass_nonneg p hp) _ _).trans
    (add_le_add (siteDegree_bad_probability p hp hpone H hHdiag hgap hmean hsquareH)
      (siteTotalSquare_bad_probability p hp hpone E hEdiag hQ hsquareE))

end JointDickman

end OAI

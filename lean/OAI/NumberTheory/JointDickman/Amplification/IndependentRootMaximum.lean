import OAI.NumberTheory.JointDickman.Amplification.FiniteExponentialMaximum

namespace OAI

/-! # Maximization over finitely many tests of independent auxiliary roots -/

namespace JointDickman
open Finset
open PublishedInputs

theorem independent_root_mgf {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (w Y : ι → Ω → ℝ) (hw : ∀ i x, 0 ≤ w i x) (hwone : ∀ i, (∑ x, w i x) = 1)
    {a : ℝ} (ha : 0 ≤ a) (hY : ∀ i x, 0 ≤ Y i x ∧ Y i x ≤ a)
    (σ : ι → ℝ) (hσ : ∀ i, |σ i| ≤ 2) {t : ℝ} (ht : 0 ≤ t) (hsmall : 2*t*a ≤ 1) :
    finiteExpectation (siteProductMass w)
      (fun x => Real.exp (t*∑ i, σ i*(Y i (x i)-finiteExpectation (w i) (Y i)))) ≤
        Real.exp (4*t^2*a*(∑ i, finiteExpectation (w i) (Y i))) := by
  have hexp (x : ι → Ω) :
      Real.exp (t*∑ i, σ i*(Y i (x i)-finiteExpectation (w i) (Y i))) =
        ∏ i, Real.exp (t*(σ i*(Y i (x i)-finiteExpectation (w i) (Y i)))) := by
    rw [mul_sum,Real.exp_sum]
  simp_rw [hexp]
  rw [siteProduct_expectation_prod w
    (fun i x => Real.exp (t*(σ i*(Y i x-finiteExpectation (w i) (Y i)))))]
  calc
    _ ≤ ∏ i, Real.exp (4*t^2*a*finiteExpectation (w i) (Y i)) := by
      apply prod_le_prod₀
      · intro i _
        exact finiteExpectation_nonneg _ _ (hw i) (fun _ => (Real.exp_pos _).le)
      · intro i _
        exact bounded_root_centered_mgf (w i) (Y i) (hw i) (hwone i) ha (hY i) (hσ i) ht hsmall
    _ = _ := by rw [← Real.exp_sum,← mul_sum]

theorem independent_root_maximum {ι Ω J : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype J] [Nonempty J]
    (w Y : ι → Ω → ℝ) (hw : ∀ i x, 0 ≤ w i x) (hwone : ∀ i, (∑ x, w i x) = 1)
    {a : ℝ} (ha : 0 ≤ a) (hY : ∀ i x, 0 ≤ Y i x ∧ Y i x ≤ a)
    (σ : J → ι → ℝ) (hσ : ∀ j i, |σ j i| ≤ 2)
    {t : ℝ} (ht : 0 < t) (hsmall : 2*t*a ≤ 1) :
    finiteExpectation (siteProductMass w)
      (finiteFamilyMaximum (fun j x => ∑ i, σ j i*(Y i (x i)-finiteExpectation (w i) (Y i)))) ≤
        (Real.log (Fintype.card J)+4*t^2*a*(∑ i, finiteExpectation (w i) (Y i)))/t := by
  apply finite_maximum_mgf (siteProductMass w) (siteProductMass_nonneg w hw)
    (siteProductMass_sum w hwone) _ ht
  intro j
  exact independent_root_mgf w Y hw hwone ha hY (σ j) (hσ j) ht.le hsmall

end JointDickman

end OAI

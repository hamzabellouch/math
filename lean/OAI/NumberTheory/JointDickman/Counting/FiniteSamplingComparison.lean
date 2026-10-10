import OAI.NumberTheory.JointDickman.Amplification.SampledColumnTail

namespace OAI

/-! # Quantitative comparison with the fully adaptive cut

The finite family tail is proved from McDiarmid's published input. All
remaining hypotheses here are the displayed first- and second-moment and
single-site-test inequalities used by the manuscript's application.
-/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype A] [DecidableEq A]

theorem finiteSamplingComparison (hMC : FiniteMcDiarmidInput ι A)
    (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (hpone : ∀ i, ∑ a, p i a = 1)
    (E H : ι → ι → A → A → ℝ)
    (hEsym : ∀ i j a b, E i j a b = E j i b a)
    (hHsym : ∀ i j a b, H i j a b = H j i b a)
    (hEdiag : ∀ i a, E i i a a = 0) (hHdiag : ∀ i a, H i i a a = 0)
    (hdom : ∀ i j a b, |E i j a b| ≤ H i j a b)
    {C q d Q e L u a : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hd : 0 < d) (hQ : 0 < Q) (hgap : C < d) (hu : 0 ≤ u)
    (hL : 0 ≤ L) (ha : 0 < a)
    (hmean : ∀ i b, |siteRowMean p H i b| ≤ C)
    (hsquareH : ∀ i, siteRowSquareMass p H i ≤ q)
    (hsquareE : ∀ i, siteRowSquareMass p E i ≤ q)
    (htest : ∀ g h : ι → A → ℝ, (∀ i b, |g i b| ≤ 1) → (∀ i b, |h i b| ≤ 1) →
      siteTestMean p E g h ≤ (Fintype.card ι : ℝ)*e)
    (hbad : (Fintype.card ι : ℝ)*q/(d-C)^2 < 1)
    (hbound : e + Real.sqrt q + L*((Fintype.card ι : ℝ)*q/(d-C)^2) ≤ u)
    (hcut : u+a < L) (m : ℕ) (hm : 0 < m) :
    finiteExpectation (siteProductMass p)
      (fun x => kernelCutNorm (realizedSiteKernel E x)) ≤
      u+a + samplingError (ι := ι) d Q m +
        Real.sqrt ((C^2+q)*((Fintype.card ι : ℝ)*q/(d-C)^2+
          (Fintype.card ι : ℝ)*q/Q +
          (((2*Fintype.card ι)^m : ℕ) : ℝ)*
            Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)))) := by
  let G := SiteKernelGood E H d Q
  have htail (s : ColumnSample (ι := ι) m) :
      finiteProbability (siteProductMass p)
        (fun x => G x ∧ u+a < columnSampleNorm (realizedSiteKernel E x) s) ≤
        Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2)) := by
    refine (finiteProbability_mono _ (siteProductMass_nonneg p hp) ?_).trans
      (sampledColumn_tail hMC p hp hpone E H hEsym hHsym hEdiag hHdiag hdom
        hC hd hgap hL ha hmean hsquareH hsquareE htest hbad hbound hcut s)
    intro x hx
    exact ⟨hx.1.1,hx.2⟩
  have hsquare : ∀ i, (∑ j, finiteExpectation (siteProductMass p)
      (fun x => H i j (x i) (x j)^2)) ≤ q := by
    intro i
    rw [← siteRowSquareMass_eq_sum_entries p hpone H hHdiag i]
    exact hsquareH i
  have hthreshold : 0 ≤ u+a+samplingError (ι := ι) d Q m := by
    apply add_nonneg (add_nonneg hu ha.le)
    unfold samplingError
    positivity
  have hb := siteKernel_sampling_transfer p hp hpone E H G hdom hHdiag hEsym
    C q d Q (u+a) (Real.exp (-(a^2*(Fintype.card ι : ℝ))/(8*d^2))) m hm hq
    hmean hsquare hthreshold
    (fun x hx i => (sum_le_sum fun j _ => hdom i j (x i) (x j)).trans (hx.1 i))
    (fun _ hx => hx.2) htail
  refine hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt ?_))
  apply mul_le_mul_of_nonneg_left _ (add_nonneg (sq_nonneg C) hq)
  exact add_le_add (siteKernelGood_bad_probability p hp hpone E H hEdiag hHdiag
    hgap hQ hmean hsquareH hsquareE) le_rfl

end JointDickman

end OAI

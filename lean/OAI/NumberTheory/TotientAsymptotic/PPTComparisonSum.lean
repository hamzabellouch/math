import OAI.NumberTheory.TotientAsymptotic.PPTTailParameters

namespace OAI

/-!
Finite summation of the fixed-common-factor, fixed-left-tail comparison
blocks in Ford's proof of (5.23).  The published comparison predicates
remain explicit.  The extra factor from fixing the left tail is bounded
by its already proved normality estimate.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The part of the comparison bound independent of the two fixed
integer factors. -/
def pptComparisonScale (C : ℝ) (b : ℕ) (z W : ℝ) (Y U : ℕ → ℝ) : ℝ :=
  (C*B z)^(6*b) * (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1) *
    (Real.log z)^(-2 + (∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B z)) +
      comparisonError b z W Y U)

lemma ppt_comparison_scale_nonneg {C z W : ℝ} {b : ℕ} {Y U : ℕ → ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B z) (hz : 1 ≤ z) (hY : 1 ≤ Y b) :
    0 ≤ pptComparisonScale C b z W Y U := by
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlogY : 0 ≤ Real.log (Y b) := Real.log_nonneg hY
  unfold pptComparisonScale
  positivity

lemma ppt_comparison_bound_factor (C : ℝ) (b d c t : ℕ) (z W : ℝ)
    (Y U : ℕ → ℝ) :
    fordComparisonBound C b z W (d*t.totient) c.totient Y U =
      z/(d : ℝ) * pptComparisonScale C b z W Y U *
        (1/(c.totient : ℝ)) * (1/(t.totient : ℝ)) *
        (b+1 : ℝ)^((d*t.totient).primeFactorsList.length) := by
  simp only [fordComparisonBound, pptComparisonScale, Nat.cast_mul,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

lemma ppt_comparison_block_sum {C z W K : ℝ} {b d : ℕ} {Y U : ℕ → ℝ}
    (hz : 0 ≤ z) (hscale : 0 ≤ pptComparisonScale C b z W Y U)
    (R A : Finset ℕ) (T : ℕ → ℕ → Finset ℕ)
    (hcount : ∀ c ∈ R, ∀ t ∈ A,
      ((T c t).card : ℝ) ≤ fordComparisonBound C b z W (d*t.totient) c.totient Y U)
    (hcost : ∀ t ∈ A, (b+1 : ℝ)^((d*t.totient).primeFactorsList.length) ≤ K) :
    (∑ c ∈ R, ∑ t ∈ A, ((T c t).card : ℝ)) ≤
      z/(d : ℝ) * pptComparisonScale C b z W Y U * K *
        (∑ c ∈ R, 1/(c.totient : ℝ)) * (∑ t ∈ A, 1/(t.totient : ℝ)) := by
  have hcommon : 0 ≤ z/(d : ℝ) * pptComparisonScale C b z W Y U :=
    mul_nonneg (div_nonneg hz (by positivity)) hscale
  calc
    _ ≤ ∑ c ∈ R, ∑ t ∈ A,
        z/(d : ℝ) * pptComparisonScale C b z W Y U * K *
          (1/(c.totient : ℝ)) * (1/(t.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro t ht
      calc
        _ ≤ fordComparisonBound C b z W (d*t.totient) c.totient Y U := hcount c hc t ht
        _ = (z/(d : ℝ) * pptComparisonScale C b z W Y U *
            (1/(c.totient : ℝ)) * (1/(t.totient : ℝ))) *
              (b+1 : ℝ)^((d*t.totient).primeFactorsList.length) := by
          rw [ppt_comparison_bound_factor]
        _ ≤ (z/(d : ℝ) * pptComparisonScale C b z W Y U *
            (1/(c.totient : ℝ)) * (1/(t.totient : ℝ))) * K := by
          apply mul_le_mul_of_nonneg_left (hcost t ht)
          exact mul_nonneg (mul_nonneg hcommon (by positivity)) (by positivity)
        _ = _ := by ring
    _ = _ := by
      symm
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

/-- The total of the actual comparison blocks is bounded by the two
reciprocal totient masses and the explicit normal-tail cost.  All input
conditions are arithmetic or the literal Ford comparison predicates. -/
theorem ppt_normal_tail_comparison_sum :
    ∃ C z₀ : ℝ, 0 < C ∧ 1 < z₀ ∧
    ∀ (b d h : ℕ) (z W V : ℝ) (Y U : ℕ → ℝ)
      (R A : Finset ℕ) (T : ℕ → ℕ → Finset ℕ)
      (tail : ℕ → Fin h → ℕ)
      (p q : ℕ → ℕ → ℕ → Fin b → ℕ) (e : ℕ → ℕ → ℕ → ℕ),
      0 < d → z₀ ≤ z → 0 ≤ B z → 1 < W → 0 ≤ B W → W ≤ V → 1 ≤ Y b →
      (∀ t ∈ A, t = ∏ i, tail t i) →
      (∀ t ∈ A, Function.Injective (tail t)) →
      (∀ t ∈ A, ∀ i, IsNormalPrime W (tail t i)) →
      (∀ t ∈ A, ∀ i, (largestPrimeFactor (tail t i-1) : ℝ) ≤ V) →
      (∀ c ∈ R, ∀ t ∈ A,
        FordComparisonParameters b z W (d*t.totient) c.totient Y U) →
      (∀ c ∈ R, ∀ t ∈ A, ∀ n ∈ T c t, n = c*t*∏ i, p c t n i) →
      (∀ c ∈ R, ∀ t ∈ A, ∀ n ∈ T c t,
        FordComparisonConditions b z W (d*t.totient) c.totient Y U
          (pptFixedComparisonPair (p c t n) (q c t n) (e c t n))) →
      (∑ c ∈ R, ∑ t ∈ A, ((T c t).card : ℝ)) ≤
        z/(d : ℝ) * pptComparisonScale C b z W Y U *
          ((b+1 : ℝ)^d.primeFactorsList.length *
            Real.exp (4*(h : ℝ)*B V*Real.log (b+1))) *
          (∑ c ∈ R, 1/(c.totient : ℝ)) * (∑ t ∈ A, 1/(t.totient : ℝ)) := by
  obtain ⟨C, z₀, hC, hz₀, hcount⟩ := ppt_fixed_comparison_count
  refine ⟨C, z₀, hC, hz₀, ?_⟩
  intro b d h z W V Y U R A T tail p q e hd hz hB hW hBW hWV hY
    htail hinj hnormal hsmall hparams hreal hconditions
  apply ppt_comparison_block_sum (zero_lt_one.trans (hz₀.trans_le hz)).le
    (ppt_comparison_scale_nonneg hC.le hB (hz₀.trans_le hz).le hY) R A T
  · intro c hc t ht
    exact hcount b d c t z W Y U hz (hparams c hc t ht) (T c t)
      (p c t) (q c t) (e c t) (hreal c hc t ht) (hconditions c hc t ht)
  · intro t ht
    rw [htail t ht]
    exact ppt_small_tail_comparison_cost b (tail t) hd (hnormal t ht)
      (hinj t ht) hW hBW hWV (hsmall t ht)

/-- Coverage by the concrete blocks suffices; blocks need not be
disjoint, and candidate totients need not be distinct. -/
lemma ppt_count_le_comparison_blocks (S R A : Finset ℕ) (T : ℕ → ℕ → Finset ℕ)
    (hcover : S ⊆ R.biUnion (fun c => A.biUnion (T c))) :
    (S.card : ℝ) ≤ ∑ c ∈ R, ∑ t ∈ A, ((T c t).card : ℝ) := by
  have hnat : S.card ≤ ∑ c ∈ R, ∑ t ∈ A, (T c t).card := by
    apply (Finset.card_le_card hcover).trans
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun c _ => Finset.card_biUnion_le)
  exact_mod_cast hnat

end TotientAsymptotic

end

end OAI

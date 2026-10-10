import OAI.Probability.SLE.Multipoint.MultipointCutoff

namespace OAI

/-! The terminal probability step for the multipoint product. Analytic
estimates enter through the expected stopped product and its deterministic
lower bound on success; completed points have already been frozen. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace SLEExactGauge.Multipoint

lemma measure_le_of_eventual_stopped_products
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (cutoff : ℕ → Set Ω) (X : ℕ → Ω → ℝ≥0∞)
    (q : ℝ) (hq : 0 < q)
    (hcover : ∀ ω ∈ E, ∀ᶠ n : ℕ in atTop, ω ∈ cutoff n)
    (hm : ∀ n, AEMeasurable (X n) P)
    (hmean : ∀ n, (∫⁻ ω, X n ω ∂P) ≤ 1)
    (hterminal : ∀ n ω, ω ∈ cutoff n → ENNReal.ofReal q ≤ X n ω) :
    P E ≤ ENNReal.ofReal q⁻¹ := by
  apply measure_le_of_eventual_cutoffs P E cutoff _ hcover
  intro n
  have hsub : cutoff n ⊆ {ω | ENNReal.ofReal q ≤ X n ω} := hterminal n
  have hb := (measure_mono hsub).trans
    (meas_ge_le_lintegral_div (hm n) (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top)
  have hle : (∫⁻ ω, X n ω ∂P) / ENNReal.ofReal q ≤ 1 / ENNReal.ofReal q := by
    exact mul_le_mul' (hmean n) le_rfl
  apply hb.trans
  simpa only [one_div, ENNReal.ofReal_inv_of_pos hq] using hle

def successBarrier (p K : ℝ) {ι : Type*} (s : Finset ι) (U : ι → ℝ) : ℝ :=
  Real.exp (-K) * (3 : ℝ)^(-(s.card : ℤ)) * Real.exp (p/2 * ∑ i ∈ s, U i)

lemma successBarrier_pos (p K : ℝ) {ι : Type*} (s : Finset ι) (U : ι → ℝ) :
    0 < successBarrier p K s U := by unfold successBarrier; positivity

lemma successBarrier_inv (p K : ℝ) {ι : Type*} (s : Finset ι) (U : ι → ℝ) :
    (successBarrier p K s U)⁻¹ =
      (3 : ℝ)^s.card * Real.exp K * Real.exp (-p/2 * ∑ i ∈ s, U i) := by
  unfold successBarrier
  rw [mul_inv_rev, mul_inv_rev, ← Real.exp_neg, ← Real.exp_neg]
  simp only [neg_neg, zpow_neg, inv_inv, zpow_natCast]
  rw [show -(p/2 * ∑ i ∈ s, U i) = -p/2 * ∑ i ∈ s, U i by ring]
  ring

lemma radius_target_exponential {a p b e : ℝ} (ha : 0 < a)
    (hb : 0 < b) (he : 0 < e) :
    Real.exp (-p/2 * (1/(2*a)*Real.log (b/e))) = (e/b)^(p/(4*a)) := by
  rw [Real.rpow_def_of_pos (div_pos he hb), Real.log_div he.ne' hb.ne',
    Real.log_div hb.ne' he.ne']
  congr 1
  field_simp
  ring

lemma radius_targets_exponential {ι : Type*} (s : Finset ι)
    {a p : ℝ} (ha : 0 < a) (b e : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (he : ∀ i ∈ s, 0 < e i) :
    Real.exp (-p/2 * ∑ i ∈ s, (1/(2*a)*Real.log (b i/e i))) =
      ∏ i ∈ s, (e i/b i)^(p/(4*a)) := by
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_congr rfl (fun i hi => radius_target_exponential ha (hb i hi) (he i hi))

end SLEExactGauge.Multipoint

end

end OAI

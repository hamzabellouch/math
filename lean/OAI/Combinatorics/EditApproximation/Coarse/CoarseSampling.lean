import OAI.Combinatorics.EditApproximation.Probability.ThresholdMoments
import OAI.Combinatorics.EditApproximation.Probability.FiniteSampling
import OAI.Combinatorics.EditApproximation.Probability.Concentration

namespace OAI

/-!
# Independent heterogeneous coarse threshold samples

Every child has its own fixed true cost and an independent uniform label
in `1,...,B`. The child estimates are absent from this probability space:
they enter only the pathwise reconstruction proved separately.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem coarse_sum_labels (B : ℕ) (value : ℕ → ℝ) :
    (∑ draw : Fin B, value (draw.val + 1)) = ∑ r ∈ Icc 1 B, value r := by
  refine sum_bij (fun draw _ => draw.val + 1) ?_ ?_ ?_ ?_
  · intro draw hdraw
    exact mem_Icc.mpr ⟨by omega, by have := draw.isLt; omega⟩
  · intro first hfirst second hsecond hequal
    exact Fin.ext (by omega)
  · intro r hr
    obtain ⟨hlower, hupper⟩ := mem_Icc.mp hr
    refine ⟨⟨r - 1, by omega⟩, mem_univ _, ?_⟩
    change r - 1 + 1 = r
    omega
  · intro draw hdraw
    rfl

noncomputable def coarseThresholdSample {B : ℕ} (scale value : ℝ) (draw : Fin B) : ℝ :=
  thresholdContribution (scale * (draw.val + 1 : ℕ) / B) scale value

theorem coarseThresholdSample_large {B : ℕ} [NeZero B] (scale value : ℝ)
    (hscale : 0 ≤ scale) (hvalue : scale ≤ value) (draw : Fin B) :
    coarseThresholdSample scale value draw = value := by
  have hB : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
  have hdraw : (draw.val + 1 : ℝ) ≤ B := by exact_mod_cast Nat.succ_le_of_lt draw.isLt
  have hthreshold : scale * (draw.val + 1 : ℕ) / B ≤ value := by
    apply le_trans _ hvalue
    apply (div_le_iff₀ hB).2
    exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using hdraw) hscale
  simp only [coarseThresholdSample, thresholdContribution, hthreshold, ↓reduceIte,
    max_eq_left hvalue]

/-- The mean, centered range and variance proxy are established for each
fixed cost, including the deterministic range above the threshold scale. -/
theorem coarseThresholdSample_moments {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (scale value : ℝ) (hscale : 0 < scale) (hvalue : 0 ≤ value) :
    (0 ≤ value - uniformMean (coarseThresholdSample (B := B) scale value) ∧
      value - uniformMean (coarseThresholdSample (B := B) scale value) ≤ scale / B) ∧
    (∀ draw : Fin B, |coarseThresholdSample scale value draw -
      uniformMean (coarseThresholdSample (B := B) scale value)| ≤ scale) ∧
    (∫ draw, (coarseThresholdSample scale value draw -
      uniformMean (coarseThresholdSample (B := B) scale value)) ^ 2
      ∂(PMF.uniformOfFintype (Fin B)).toMeasure) ≤ scale * value := by
  have hB : 0 < B := Nat.pos_of_ne_zero (NeZero.ne B)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  by_cases hlarge : scale ≤ value
  · have hconstant : coarseThresholdSample (B := B) scale value = fun _ => value := by
      funext draw
      exact coarseThresholdSample_large scale value hscale.le hlarge draw
    rw [hconstant]
    have hmean : uniformMean (fun _ : Fin B => value) = value := by
      simp only [uniformMean, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp only [hmean, sub_self, abs_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact ⟨⟨le_rfl, div_nonneg hscale.le hBr.le⟩, fun _ => hscale.le,
      mul_nonneg hscale.le hvalue⟩
  · have hsmall : value < scale := lt_of_not_ge hlarge
    have hmean : uniformMean (coarseThresholdSample (B := B) scale value) =
        (∑ r ∈ Icc 1 B, thresholdContribution (scale * r / B) scale value) / B := by
      simp only [uniformMean, Fintype.card_fin, coarseThresholdSample]
      rw [coarse_sum_labels B (fun r => thresholdContribution (scale * r / B) scale value)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmean]
      exact threshold_bias B scale value hB hscale hvalue hsmall
    · apply uniform_centered_bound
      intro draw
      unfold coarseThresholdSample thresholdContribution
      split_ifs
      · exact ⟨hscale.le.trans (le_max_right _ _), by rw [max_eq_right hsmall.le]⟩
      · exact ⟨le_rfl, hscale.le⟩
    · rw [uniform_integral]
      simp only [uniformMean, Fintype.card_fin, coarseThresholdSample]
      rw [coarse_sum_labels B (fun r => thresholdContribution (scale * r / B) scale value)]
      rw [coarse_sum_labels B (fun r =>
        (thresholdContribution (scale * r / B) scale value -
          (∑ s ∈ Icc 1 B, thresholdContribution (scale * s / B) scale value) / B) ^ 2)]
      exact threshold_variance_bound B scale value hB hscale hvalue hsmall

/-- Actual product-uniform child labels satisfy the manuscript's coarse
Bernstein tail bound for every fixed heterogeneous true-cost list. -/
theorem coarse_product_threshold_concentration_positive {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (value : Fin B → ℝ) (scale allowance Q lam : ℝ)
    (hvalue : ∀ i, 0 ≤ value i) (hu : 0 < scale) (ha : 0 < allowance)
    (hQ : Q * scale = allowance) (hscale : scale ≤ allowance / 2)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (hV : 0 < ∑ i, value i)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | lam * (∑ i, value i) + allowance <
        |(∑ i, coarseThresholdSample scale (value i) (draws i)) - ∑ i, value i|} ≤
      2 * Real.exp (-lam * Q / 12) := by
  let μ := (PMF.uniformOfFintype (Fin B)).toMeasure
  let sample := fun i => coarseThresholdSample (B := B) scale (value i)
  let mean := ∑ i, uniformMean (sample i)
  let X : Fin B → (Fin B → Fin B) → ℝ :=
    fun i draws => sample i (draws i) - uniformMean (sample i)
  have hmoments (i : Fin B) := coarseThresholdSample_moments (B := B) scale (value i) hu (hvalue i)
  have hindep : iIndepFun X (Measure.pi fun _ : Fin B => μ) :=
    iIndepFun_pi (μ := fun _ : Fin B => μ)
      (X := fun i draw => sample i draw - uniformMean (sample i))
      (fun _ => (measurable_of_finite _).aemeasurable)
  have hcenter (i : Fin B) : (∫ draws, X i draws ∂Measure.pi (fun _ : Fin B => μ)) = 0 := by
    dsimp [X]
    rw [integral_comp_eval (μ := fun _ : Fin B => μ) (i := i)
      (f := fun draw => sample i draw - uniformMean (sample i))
      (measurable_of_finite _).aestronglyMeasurable]
    exact uniform_centered_integral (sample i)
  have hbound (i : Fin B) : ∀ᵐ draws ∂Measure.pi (fun _ : Fin B => μ), |X i draws| ≤ scale := by
    filter_upwards [] with draws
    exact (hmoments i).2.1 (draws i)
  have hvariance : (∑ i, ∫ draws, (X i draws) ^ 2 ∂Measure.pi (fun _ : Fin B => μ)) ≤
      scale * (∑ i, value i) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    dsimp [X]
    rw [integral_comp_eval (μ := fun _ : Fin B => μ) (i := i)
      (f := fun draw => (sample i draw - uniformMean (sample i)) ^ 2)
      (measurable_of_finite _).aestronglyMeasurable]
    exact (hmoments i).2.2
  have hbias : |mean - ∑ i, value i| ≤ scale := by
    have hnonnegative := sum_nonneg (s := univ) (fun i _ => (hmoments i).1.1)
    have hsum := sum_le_sum (s := univ) (fun i _ => (hmoments i).1.2)
    have hB : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hnonnegative hsum
    have hequal : (B : ℝ) * (scale / B) = scale := by field_simp
    rw [hequal] at hsum
    dsimp [mean]
    rw [abs_of_nonpos (by linarith)]
    linarith
  exact coarse_threshold_concentration (Measure.pi fun _ : Fin B => μ) bernstein X
    (fun draws => ∑ i, sample i (draws i)) mean (∑ i, value i) lam allowance scale Q
    hlam hlamone hV ha hu hQ hscale hindep
    (fun _ => measurable_of_finite _) (fun _ => .of_finite) hcenter hbound hvariance
    (by intro draws; simp only [X, mean, sum_sub_distrib]) hbias

/-- The same exact product-uniform law, including zero total true cost. -/
theorem coarse_product_threshold_concentration {B : ℕ} [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (value : Fin B → ℝ) (scale allowance Q lam : ℝ)
    (hvalue : ∀ i, 0 ≤ value i) (hu : 0 < scale) (ha : 0 < allowance)
    (hQ : Q * scale = allowance) (hscale : scale ≤ allowance / 2)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).real
      {draws | lam * (∑ i, value i) + allowance <
        |(∑ i, coarseThresholdSample scale (value i) (draws i)) - ∑ i, value i|} ≤
      2 * Real.exp (-lam * Q / 12) := by
  by_cases hV : 0 < ∑ i, value i
  · exact coarse_product_threshold_concentration_positive value scale allowance Q lam
      hvalue hu ha hQ hscale hlam hlamone hV bernstein
  · have htotal : (∑ i, value i) = 0 := by
      have hnonnegative := sum_nonneg (s := univ) (fun i _ => hvalue i)
      linarith
    have hzero (i : Fin B) : value i = 0 := by
      have hi := single_le_sum (s := univ) (fun i _ => hvalue i) (mem_univ i)
      rw [htotal] at hi
      exact le_antisymm hi (hvalue i)
    have hsample (draw : Fin B) : coarseThresholdSample scale 0 draw = 0 := by
      have hB : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne B)
      have hdraw : (0 : ℝ) < (draw.val + 1 : ℕ) := by positivity
      have hthreshold : 0 < scale * (draw.val + 1 : ℕ) / B := by positivity
      simp only [coarseThresholdSample, thresholdContribution, not_le_of_gt hthreshold, ↓reduceIte]
    have hempty : {draws : Fin B → Fin B | lam * (∑ i, value i) + allowance <
        |(∑ i, coarseThresholdSample scale (value i) (draws i)) - ∑ i, value i|} = ∅ := by
      ext draws
      simp only [hzero, hsample, sum_const_zero, mul_zero, zero_add, sub_self, abs_zero,
        not_lt_of_ge ha.le, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [hempty, measureReal_empty]
    positivity

end EditApproximation

end OAI

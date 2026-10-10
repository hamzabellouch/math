import OAI.Combinatorics.EditApproximation.Probability.FiniteSampling

namespace OAI

/-!
# Shared group sampling

The one-scale estimator in Section 5 is a finite uniform average. Its
concentration follows from the explicitly cited Bernstein input. Choosing
among representatives and extending their costs by cones is deterministic
on the simultaneous approximation event, even when their samples are shared.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def normalizedChildSample {M : ℕ} (b h : ℝ)
    (childScale childValue : Fin M → ℝ) (i : Fin M) : ℝ :=
  if childScale i = h then (M : ℝ) * childValue i / b else 0

/-- The normalized sample bounds used by the executable group estimator
follow from the rounded action's child bounds and the band sum guard. -/
theorem normalizedChildSample_moments {M : ℕ} (hM : 0 < M)
    (b h F : ℝ) (hb : 0 < b) (hh : 0 < h)
    (childScale childValue : Fin M → ℝ)
    (hscale : ∀ i, 0 ≤ childScale i)
    (hvalue : ∀ i, 0 ≤ childValue i ∧ childValue i ≤ 2 * childScale i)
    (hsum : (∑ i, childScale i) ≤ 64 * F * b) :
    (∀ i, 0 ≤ normalizedChildSample b h childScale childValue i ∧
      normalizedChildSample b h childScale childValue i ≤ 2 * ((M : ℝ) * h / b)) ∧
    uniformMean (normalizedChildSample b h childScale childValue) ≤ 128 * F := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hpoint (i : Fin M) : normalizedChildSample b h childScale childValue i ≤
      (M : ℝ) / b * (2 * childScale i) := by
    unfold normalizedChildSample
    split_ifs
    · have hmul := mul_le_mul_of_nonneg_left (hvalue i).2 (div_nonneg hMr.le hb.le)
      convert hmul using 1
      ring
    · exact mul_nonneg (div_nonneg hMr.le hb.le)
        (mul_nonneg (by norm_num) (hscale i))
  constructor
  · intro i
    unfold normalizedChildSample
    split_ifs with hi
    · constructor
      · exact div_nonneg (mul_nonneg hMr.le (hvalue i).1) hb.le
      · have hmul := mul_le_mul_of_nonneg_left (hvalue i).2 hMr.le
        rw [hi] at hmul
        calc
          _ ≤ (2 * ((M : ℝ) * h)) / b :=
            div_le_div_of_nonneg_right (by nlinarith :
              (M : ℝ) * childValue i ≤ 2 * ((M : ℝ) * h)) hb.le
          _ = _ := by ring
    · constructor
      · rfl
      · positivity
  · unfold uniformMean
    rw [Fintype.card_fin]
    apply (div_le_iff₀ hMr).2
    have hsumPoint := sum_le_sum (s := univ) fun i _ => hpoint i
    rw [← mul_sum, ← mul_sum] at hsumPoint
    have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * M / b)
    have hid : (M : ℝ) / b * (2 * ∑ i, childScale i) =
        (2 * M / b) * ∑ i, childScale i := by ring
    rw [hid] at hsumPoint
    have hcancel : (2 * M / b) * (64 * F * b) = 128 * F * M := by field_simp; ring
    rw [hcancel] at hscaled
    linarith

theorem group_bernstein_exponent {ratio F Q deviation : ℝ} {n : ℕ}
    (hratio : 0 < ratio) (hF : 0 < F) (hdev : 0 < deviation)
    (hsamples : Q * ratio ≤ n) :
    Q * deviation ^ 2 / (512 * F + (4 / 3 : ℝ) * deviation) ≤
      (n : ℝ) * deviation ^ 2 /
        (2 * (2 * ratio) * (128 * F) + (2 / 3 : ℝ) * (2 * ratio) * deviation) := by
  let den := 512 * F + (4 / 3 : ℝ) * deviation
  have hden : 0 < den := by dsimp [den]; positivity
  have hid : 2 * (2 * ratio) * (128 * F) + (2 / 3 : ℝ) * (2 * ratio) * deviation =
      ratio * den := by dsimp [den]; ring
  rw [hid]
  apply (div_le_div_iff₀ hden (mul_pos hratio hden)).2
  have hmul := mul_le_mul_of_nonneg_right hsamples
    (mul_nonneg (sq_nonneg deviation) hden.le)
  nlinarith

theorem group_scale_concentration {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (n : ℕ) (hn : 0 < n) (value : ι → ℝ) (ratio F Q deviation : ℝ)
    (hratio : 0 < ratio) (hF : 0 < F) (hdev : 0 < deviation)
    (hvalue : ∀ i, 0 ≤ value i ∧ value i ≤ 2 * ratio)
    (hmean : uniformMean value ≤ 128 * F) (hsamples : Q * ratio ≤ n)
    (bernstein : FiniteBernsteinInput
      (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure)) :
    (Measure.pi fun _ : Fin n => (PMF.uniformOfFintype ι).toMeasure).real
      {ω | deviation ≤ |(∑ j : Fin n, value (ω j)) / n - uniformMean value|} ≤
      2 * Real.exp (-Q * deviation ^ 2 / (512 * F + (4 / 3 : ℝ) * deviation)) := by
  have htail := uniform_sample_average_concentration n hn value
    (2 * ratio) (128 * F) deviation (by positivity) (by positivity) hdev
    hvalue hmean bernstein
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div, neg_mul] using
    neg_le_neg (group_bernstein_exponent hratio hF hdev hsamples)

/-- Shared draws may correlate all representatives. The simultaneous
event uses only finite subadditivity. -/
theorem group_failure_union_bound {Ω ι κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (members : Finset ι) (scales : Finset κ)
    (bad : ι → κ → Set Ω) (failure : ℝ)
    (hfailure : ∀ i ∈ members, ∀ h ∈ scales, μ.real (bad i h) ≤ failure) :
    μ.real (⋃ i ∈ members, ⋃ h ∈ scales, bad i h) ≤
      (members.card : ℝ) * scales.card * failure := by
  apply (measureReal_biUnion_finset_le members _).trans
  have hmember (i : ι) (hi : i ∈ members) :
      μ.real (⋃ h ∈ scales, bad i h) ≤ (scales.card : ℝ) * failure := by
    apply (measureReal_biUnion_finset_le scales _).trans
    have hsum := sum_le_sum (s := scales) fun h hh => hfailure i hi h hh
    simpa only [sum_const, nsmul_eq_mul] using hsum
  have hsum := sum_le_sum hmember
  simpa only [sum_const, nsmul_eq_mul, mul_assoc] using hsum

theorem group_scale_errors_sum {κ : Type*} (scales : Finset κ)
    (estimate cost : κ → ℝ) (deviation : ℝ)
    (herror : ∀ h ∈ scales, |estimate h - cost h| ≤ deviation) :
    |(∑ h ∈ scales, estimate h) - (∑ h ∈ scales, cost h)| ≤
      (scales.card : ℝ) * deviation := by
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hsum := sum_le_sum herror
  simpa only [sum_const, nsmul_eq_mul] using hsum

/-- Estimated-cost minimization followed by actual evaluation loses at
most twice the uniform estimation error. There is no probabilistic
independence premise in this selection step. -/
theorem selected_group_cost_le {ι : Type*} (members : Finset ι)
    (cost estimate : ι → ℝ) (selected specified : ι) (error : ℝ)
    (hselected : selected ∈ members) (hspecified : specified ∈ members)
    (haccurate : ∀ i ∈ members, |estimate i - cost i| ≤ error)
    (hmin : estimate selected ≤ estimate specified) :
    cost selected ≤ cost specified + 2 * error := by
  have hs := (abs_le.mp (haccurate selected hselected)).1
  have hr := (abs_le.mp (haccurate specified hspecified)).2
  linarith

theorem selected_group_cone_bound {ι : Type*} (members : Finset ι)
    (cost estimate distance : ι → ℝ) (selected specified : ι)
    (cone L radius error roundedAction : ℝ)
    (hselected : selected ∈ members) (hspecified : specified ∈ members)
    (haccurate : ∀ i ∈ members, |estimate i - cost i| ≤ error)
    (hmin : estimate selected ≤ estimate specified)
    (hcone : cone ≤ cost selected + L * distance selected)
    (hL : 0 ≤ L) (hcell : distance selected ≤ distance specified + radius)
    (hrounded : cost specified ≤ roundedAction) :
    cone ≤ L * distance specified + roundedAction + 2 * error + L * radius := by
  have hcost := selected_group_cost_le members cost estimate selected specified error
    hselected hspecified haccurate hmin
  have hdist := mul_le_mul_of_nonneg_left hcell hL
  linarith

end EditApproximation

end OAI

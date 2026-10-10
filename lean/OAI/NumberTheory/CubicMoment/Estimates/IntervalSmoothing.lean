import OAI.NumberTheory.CubicMoment.Estimates.EndpointKernel

namespace OAI

/-!
# The endpoint error of a smoothed interval

A normalized integrable kernel approximates an interval indicator with
error controlled by its two tails. The proof retains exact endpoints.
This is the physical-space step of the Fourier truncation argument.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def intervalStep (a b s : ℝ) : ℝ := if s ∈ Set.Icc a b then 1 else 0

def intervalSmoothing (k : ℝ → ℂ) (a b s : ℝ) : ℂ :=
  ∫ y, (intervalStep a b (s - y) : ℂ) * k y

/-- A shift smaller than the distance to both endpoints preserves membership. -/
theorem intervalStep_eq_of_away {a b s y : ℝ}
    (ha : |y| < |s - a|) (hb : |y| < |s - b|) :
    intervalStep a b (s - y) = intervalStep a b s := by
  have hae : a ≤ s - y ↔ a ≤ s := by
    by_cases h : a ≤ s
    · rw [abs_of_nonneg (sub_nonneg.mpr h)] at ha
      have hy := le_abs_self y
      constructor <;> intro <;> linarith
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at ha
      have hy := neg_abs_le y
      constructor <;> intro <;> linarith
  have hbe : s - y ≤ b ↔ s ≤ b := by
    by_cases h : s ≤ b
    · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hb
      have hy := neg_abs_le y
      constructor <;> intro <;> linarith
    · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge h))] at hb
      have hy := le_abs_self y
      constructor <;> intro <;> linarith
  simp only [intervalStep, Set.mem_Icc, hae, hbe]

/-- Any change in the indicator crosses at least one endpoint. -/
theorem intervalStep_jump_le (a b s y : ℝ) :
    |intervalStep a b s - intervalStep a b (s - y)| ≤
      (if |s - a| ≤ |y| then (1 : ℝ) else 0) +
      (if |s - b| ≤ |y| then (1 : ℝ) else 0) := by
  have hone : |intervalStep a b s - intervalStep a b (s - y)| ≤ 1 := by
    unfold intervalStep
    split_ifs <;> norm_num
  by_cases ha : |s - a| ≤ |y|
  · by_cases hb : |s - b| ≤ |y| <;> simp only [ha, hb, ite_true, ite_false] <;> linarith
  · by_cases hb : |s - b| ≤ |y|
    · simpa only [ha, hb, ite_true, ite_false, zero_add] using hone
    · rw [intervalStep_eq_of_away (lt_of_not_ge ha) (lt_of_not_ge hb)]
      simp [ha, hb]

theorem integrable_intervalSmoothing_integrand {k : ℝ → ℂ} (hk : Integrable k)
    (a b s : ℝ) : Integrable (fun y => (intervalStep a b (s-y) : ℂ) * k y) := by
  have hm : MeasurableSet {y : ℝ | s-y ∈ Set.Icc a b} :=
    measurableSet_Icc.preimage (measurable_const.sub measurable_id)
  have heq : (fun y => (intervalStep a b (s-y) : ℂ) * k y) =
      {y : ℝ | s-y ∈ Set.Icc a b}.indicator k := by
    funext y
    by_cases hy : s-y ∈ Set.Icc a b <;>
      simp only [intervalStep, Set.indicator_apply, Set.mem_ofPred_eq, hy,
        ite_true, ite_false, Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul]
  rw [heq]
  exact hk.indicator hm

/-- The smoothed indicator has an error bounded by the kernel mass beyond
the distances to the two endpoints. No positivity of the kernel is needed. -/
theorem intervalSmoothing_error_le_tails {k : ℝ → ℂ} (hk : Integrable k)
    (hmass : ∫ y, k y = 1) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing k a b s‖ ≤
      (∫ y, if |s-a| ≤ |y| then ‖k y‖ else 0) +
      (∫ y, if |s-b| ≤ |y| then ‖k y‖ else 0) := by
  have hshift := integrable_intervalSmoothing_integrand hk a b s
  have hconst := hk.const_mul (intervalStep a b s : ℂ)
  have hid : (intervalStep a b s : ℂ) - intervalSmoothing k a b s =
      ∫ y, ((intervalStep a b s : ℂ) - (intervalStep a b (s-y) : ℂ)) * k y := by
    calc
      _ = (∫ y, (intervalStep a b s : ℂ) * k y) -
          ∫ y, (intervalStep a b (s-y) : ℂ) * k y := by
        rw [integral_const_mul, hmass, mul_one]
        rfl
      _ = _ := by
        rw [← integral_sub hconst hshift]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => (sub_mul _ _ _).symm)
  have hta : Integrable (fun y => if |s-a| ≤ |y| then ‖k y‖ else 0) := by
    exact hk.norm.indicator (measurableSet_le measurable_const measurable_id.abs)
  have htb : Integrable (fun y => if |s-b| ≤ |y| then ‖k y‖ else 0) := by
    exact hk.norm.indicator (measurableSet_le measurable_const measurable_id.abs)
  rw [hid, ← integral_add hta htb]
  apply (norm_integral_le_integral_norm _).trans
  have hdiff : Integrable (fun y =>
      ((intervalStep a b s : ℂ) - (intervalStep a b (s-y) : ℂ)) * k y) := by
    apply (hconst.sub hshift).congr
    exact Filter.Eventually.of_forall (fun y => (sub_mul _ _ _).symm)
  apply integral_mono hdiff.norm (hta.add htb)
  intro y
  change ‖((intervalStep a b s : ℂ) - (intervalStep a b (s-y) : ℂ)) * k y‖ ≤
    (if |s-a| ≤ |y| then ‖k y‖ else 0) + (if |s-b| ≤ |y| then ‖k y‖ else 0)
  rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (intervalStep_jump_le a b s y) (_root_.norm_nonneg (k y))
  simpa only [add_mul, ite_mul, one_mul, zero_mul] using h

end CubicFirstMoment

end

end OAI

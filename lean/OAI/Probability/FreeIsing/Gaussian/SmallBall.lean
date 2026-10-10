import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace Problem367

theorem gaussianPDFReal_le_peak (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  have hexp : Real.exp (-(x - m) ^ 2 / (2 * v)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := mul_one _

theorem gaussianReal_le_peak_mul_volume
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal m v s ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) * volume s := by
  rw [gaussianReal_apply m hv s]
  calc
    _ ≤ ∫⁻ _ in s, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_peak m v x)
    _ = _ := by simp

theorem gaussianReal_Icc_le
    (m a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v (Set.Icc a b) ≤
      ENNReal.ofReal ((b - a) / Real.sqrt (2 * Real.pi * v)) := by
  have h := gaussianReal_le_peak_mul_volume m hv (Set.Icc a b)
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem gaussianReal_abs_le
    (m ε : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v {x | |x| ≤ ε} ≤
      ENNReal.ofReal (2 * ε / Real.sqrt (2 * Real.pi * v)) := by
  have hset : {x : ℝ | |x| ≤ ε} = Set.Icc (-ε) ε := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  rw [hset]
  convert gaussianReal_Icc_le m (-ε) ε hv using 2
  ring

theorem gaussianReal_abs_le_of_variance_ge
    (m : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {δ v : ℝ≥0}
    (hδ : 0 < δ) (hδv : δ ≤ v) :
    gaussianReal m v {x | |x| ≤ ε} ≤
      ENNReal.ofReal (2 * ε / Real.sqrt (2 * Real.pi * δ)) := by
  have hv : v ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hδv)
  apply (gaussianReal_abs_le m ε hv).trans
  apply ENNReal.ofReal_le_ofReal
  have hsqrt : Real.sqrt (2 * Real.pi * (δ : ℝ)) ≤
      Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hδv) (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) _ hsqrt
  apply Real.sqrt_pos.mpr
  exact mul_pos (by positivity) (by exact_mod_cast hδ)

def gaussianSmallRadius (δ : ℝ≥0) : ℝ :=
  Real.sqrt (2 * Real.pi * δ) / 4

lemma gaussianSmallRadius_pos {δ : ℝ≥0} (hδ : 0 < δ) :
    0 < gaussianSmallRadius δ := by
  unfold gaussianSmallRadius
  positivity

lemma gaussianReal_smallBall_le_half
    (m : ℝ) {δ v : ℝ≥0} (hδ : 0 < δ) (hδv : δ ≤ v) :
    gaussianReal m v {x | |x| ≤ gaussianSmallRadius δ} ≤ (1 / 2 : ℝ≥0∞) := by
  have h := gaussianReal_abs_le_of_variance_ge m
    (gaussianSmallRadius_pos hδ).le hδ hδv
  have hs : Real.sqrt (2 * Real.pi * (δ : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact mul_pos (by positivity) (by exact_mod_cast hδ)
  have hc : 2 * gaussianSmallRadius δ / Real.sqrt (2 * Real.pi * δ) = (1 / 2 : ℝ) := by
    unfold gaussianSmallRadius
    field_simp
    ring
  rw [hc] at h
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  simpa only [hhalf] using h

theorem smallBall_le_half_of_hasGaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {m : ℝ} {δ v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) P)
    (hδ : 0 < δ) (hδv : δ ≤ v) :
    P {ω | |X ω| ≤ gaussianSmallRadius δ} ≤ (1 / 2 : ℝ≥0∞) := by
  rw [hX.measure_eq (p := fun x : ℝ => |x| ≤ gaussianSmallRadius δ)
    (measurableSet_le measurable_id.abs measurable_const)]
  exact gaussianReal_smallBall_le_half m hδ hδv

theorem integral_le_one_sub_half_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} {s : Set Ω} {c : ℝ}
    (hf : Integrable f P) (hs : MeasurableSet s) (hc : 0 ≤ c)
    (hupper : ∀ᵐ x ∂P, f x ≤ 1)
    (houtside : ∀ᵐ x ∂P, x ∉ s → f x ≤ 1 - c)
    (hmass : P s ≤ (1 / 2 : ℝ≥0∞)) :
    ∫ x, f x ∂P ≤ 1 - c / 2 := by
  have hsreal : P.real s ≤ 1 / 2 := by
    change (P s).toReal ≤ 1 / 2
    have h := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) hmass
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hi : Integrable (fun x => (1 - c) + s.indicator (fun _ => c) x) P :=
    (integrable_const _).add ((integrable_const _).indicator hs)
  have hvalue : (∫ x, (1 - c) + s.indicator (fun _ => c) x ∂P) =
      1 - c + P.real s * c := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hs),
      integral_const, integral_indicator_const _ hs]
    simp
  have hle : ∫ x, f x ∂P ≤ ∫ x, (1 - c) + s.indicator (fun _ => c) x ∂P := by
    apply integral_mono_ae hf hi
    filter_upwards [hupper, houtside] with x hx ho
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      linarith
    · simpa only [Set.indicator_of_notMem hxs, add_zero] using ho hxs
  rw [hvalue] at hle
  nlinarith

theorem integral_gaussian_le_one_sub_half_gap
    (m : ℝ) {δ v : ℝ≥0} (hδ : 0 < δ) (hδv : δ ≤ v)
    {f : ℝ → ℝ} {c : ℝ} (hf : Integrable f (gaussianReal m v)) (hc : 0 ≤ c)
    (hupper : ∀ x, f x ≤ 1)
    (houtside : ∀ x, gaussianSmallRadius δ < |x| → f x ≤ 1 - c) :
    ∫ x, f x ∂gaussianReal m v ≤ 1 - c / 2 := by
  apply integral_le_one_sub_half_gap (gaussianReal m v) hf
    (measurableSet_le measurable_id.abs measurable_const) hc
    (Filter.Eventually.of_forall hupper)
  · exact Filter.Eventually.of_forall fun x hx => houtside x (lt_of_not_ge hx)
  · exact gaussianReal_smallBall_le_half m hδ hδv

end Problem367

end

end OAI

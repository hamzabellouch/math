import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.Combined
import OAI.Geometry.CAT0Fillings.Chord.Identity

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.Conformal
lemma weighted_kernel_average_le_one {q b : ℝ} (hq : 0 < q) (hb : 0 ≤ b) :
    q*(∫ u in (0:ℝ)..1, u^(q-1)*(1+b*u)^(-2*q-2)) ≤ 1 := by
  calc
    _ ≤ q*(∫ u in (0:ℝ)..1, u^(q-1)) := by
      apply mul_le_mul_of_nonneg_left _ hq.le
      apply intervalIntegral.integral_mono_on zero_le_one
        (ChordIdentity.integral_weighted_kernel (by linarith) hb) (ChordAverage.integrable_weight hq 1)
      intro u hu
      apply mul_le_of_le_one_right (Real.rpow_nonneg hu.1 _)
      exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [mul_nonneg hb hu.1]) (by linarith)
    _ = 1 := by rw [ChordAverage.weight_integral hq]; field_simp
lemma profile_bound {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    (chordBubble q a t)^2 + (1/(2*q))*t^2*averageProfile n (chordBubbleD q a) t ≤ 1 := by
  rw [profile_scalar_identity hn hq ha hnq t]
  exact weighted_kernel_average_le_one hq (by positivity)
lemma profile_term_bound {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q)
    (ha : 0 ≤ a) (hnq : (n:ℝ) = 2*q+2) (t : ℝ) :
    |t^2*averageProfile n (chordBubbleD q a) t| ≤ 2*q := by
  have hf0 := averageProfile_nonneg n (chordBubbleD q a) t
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hf0)]
  have h := profile_bound hn hq ha hnq t
  have hle : (1/(2*q))*(t^2*averageProfile n (chordBubbleD q a) t) ≤ 1 := by
    nlinarith [sq_nonneg (chordBubble q a t)]
  have hh := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2*q by positivity)
  field_simp at hh
  nlinarith
end CAT0Fillings.Conformal
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.Conformal
lemma bubbleProfile_continuous {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 ≤ q) (ha : 0 < a) :
    Continuous (averageProfile n (chordBubbleD q a)) := by
  obtain ⟨B,hB,hbounds⟩ := chordBubble_bounded_derivatives ha hq
  apply (averageProfile_contDiff hn (chordBubbleD_contDiff ha.le q 1) hB ?_).continuous
  intro t
  refine ⟨?_,(hbounds t).2.2⟩
  simpa only [(chordBubble_hasDerivAt ha.le q t).deriv] using (hbounds t).2.1
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
lemma profile_integrable {s : α → ℝ} (hs : AEStronglyMeasurable s μ)
    {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hnq : (n:ℝ) = 2*q+2) :
    Integrable (fun x => (chordBubble q a (s x))^2) μ ∧
      Integrable (fun x => (s x)^2*averageProfile n (chordBubbleD q a) (s x)) μ := by
  have hw := (chordBubble_contDiff ha.le q 1).continuous.comp_aestronglyMeasurable hs
  have hm := (bubbleProfile_continuous hn hq.le ha).comp_aestronglyMeasurable hs
  constructor
  · apply (MemLp.of_bound (hw.pow 2) 1 ?_).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (chordBubble_pos ha.le q _).le (chordBubble_le_one ha.le hq.le _)
  · apply (MemLp.of_bound ((hs.pow 2).mul hm) (2*q) ?_).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)
    filter_upwards [] with x
    exact profile_term_bound hn hq ha.le hnq _
lemma profile_average {s : α → ℝ} (hs : AEStronglyMeasurable s μ)
    {n : ℕ} (hn : 0 < n) {q a : ℝ} (hq : 0 < q) (ha : 0 < a)
    (hnq : (n:ℝ) = 2*q+2) :
    (∫ x, (chordBubble q a (s x))^2 ∂μ)+
      (1/(2*q))*(∫ x, (s x)^2*averageProfile n (chordBubbleD q a) (s x) ∂μ) =
    ChordAverage.average q (ChordTransform.transform μ n (fun x => (s x)^2)) a := by
  obtain ⟨hw,hf⟩ := profile_integrable μ hs hn hq ha hnq
  rw [←integral_const_mul,←integral_add hw (hf.const_mul _),
    ChordTransform.average_transform μ (b := fun x => (s x)^2) (hs.pow 2) (Eventually.of_forall fun x => sq_nonneg (s x)) hq
      (Nat.cast_nonneg n) ha.le]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [←mul_assoc,profile_scalar_identity hn hq ha.le hnq (s x)]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only [ChordTransform.kernel]
  rw [hnq,show -(2*q+2) = -2*q-2 by ring]
  congr 2
  ring
end CAT0Fillings.Conformal
end

end OAI

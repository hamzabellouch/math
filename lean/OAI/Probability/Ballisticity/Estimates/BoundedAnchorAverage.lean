import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
namespace DirectionalTransience

noncomputable def sampleAverage {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n:ℝ)⁻¹*∑ a∈Finset.range n, X a ω

lemma sampleAverage_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ a, Measurable (X a))
    (hB : ∀ a ω, |X a ω|≤1) (n : ℕ) : MemLp (sampleAverage X n) 2 μ := by
  apply MemLp.of_bound (by unfold sampleAverage; fun_prop) 1
  filter_upwards [] with ω
  dsimp only [sampleAverage]
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  have hs : ‖∑ a∈Finset.range n, X a ω‖ ≤ (n:ℝ) := by
    calc _ ≤ ∑ a∈Finset.range n, ‖X a ω‖ := norm_sum_le _ _
         _ ≤ ∑ _a∈Finset.range n, (1:ℝ) := Finset.sum_le_sum fun a _ => hB a ω
         _ = _ := by simp
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg n))).trans
  by_cases hn : n=0
  · simp [hn]
  · simp [hn]

lemma sampleAverage_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ a, Measurable (X a)) (hB : ∀ a ω, |X a ω|≤1)
    (hi : iIndepFun X μ) (n : ℕ) (hn : 0<n) :
    variance (sampleAverage X n) μ ≤ (n:ℝ)⁻¹ := by
  have hM (a : ℕ) : MemLp (X a) 2 μ :=
    MemLp.of_bound (hX a).aestronglyMeasurable 1 (Eventually.of_forall (hB a))
  have hv (a : ℕ) : variance (X a) μ ≤ 1 := by
    apply (variance_le_expectation_sq (hX a).aestronglyMeasurable).trans
    calc _ ≤ ∫ _ω, (1:ℝ) ∂μ := by
           apply integral_mono (hM a).integrable_sq (integrable_const _)
           intro ω
           dsimp
           nlinarith [hB a ω,neg_le_abs (X a ω),le_abs_self (X a ω)]
         _ = 1 := by simp
  unfold sampleAverage
  rw [variance_const_mul]
  have he : (fun ω => ∑ a∈Finset.range n, X a ω)=∑ a∈Finset.range n, X a := by
    ext ω; simp
  rw [he,IndepFun.variance_sum (fun a _ => hM a) (fun a _ b _ h => hi.indepFun h)]
  calc
    _ ≤ (n:ℝ)⁻¹^2*∑ _a∈Finset.range n, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hv a) (sq_nonneg _)
    _ = (n:ℝ)⁻¹ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
      field_simp

lemma sampleAverage_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ a, Measurable (X a)) (hB : ∀ a ω, |X a ω|≤1)
    (hi : iIndepFun X μ) (n : ℕ) (hn : 0<n) (B ε : ℝ)
    (hmean : ∀ a, (∫ ω, X a ω ∂μ)≤B) (hε : 0<ε) :
    μ {ω | B+ε<sampleAverage X n ω} ≤ ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) := by
  have hM (a : ℕ) : Integrable (X a) μ :=
    (integrable_const (1:ℝ)).mono' (hX a).aestronglyMeasurable (Eventually.of_forall (hB a))
  have hm : (∫ ω, sampleAverage X n ω ∂μ) ≤ B := by
    unfold sampleAverage
    rw [integral_const_mul,integral_finsetSum _ (fun a _ => hM a)]
    calc _ ≤ (n:ℝ)⁻¹*∑ _a∈Finset.range n, B :=
           mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hmean a) (inv_nonneg.mpr (Nat.cast_nonneg n))
         _ = B := by simp [hn.ne']
  have he : {ω | B+ε<sampleAverage X n ω} ⊆
      {ω | ε≤|sampleAverage X n ω-∫ ω, sampleAverage X n ω ∂μ|} := by
    intro ω hω
    have hle := le_abs_self (sampleAverage X n ω-∫ ω, sampleAverage X n ω ∂μ)
    dsimp at hω ⊢
    linarith
  exact (measure_mono he).trans ((meas_ge_le_variance_div_sq
    (sampleAverage_memLp μ X hX hB n) hε).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (sampleAverage_variance_le μ X hX hB hi n hn) (sq_nonneg _))))

end DirectionalTransience

end

end OAI

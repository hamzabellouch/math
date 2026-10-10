import Mathlib
import OAI.Probability.Ballisticity.Estimates.BoundaryGapReplacement

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma weighted_three_test_perturbation {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : Fin 3 → ℕ → Ω → ℝ)
    (hX : ∀ j i, Measurable (X j i)) (hY : ∀ j i, Measurable (Y j i))
    (F : ℕ → Ω → ℝ) (hF : ∀ i, Measurable (F i)) (C : ℝ) (hC : 0≤C)
    (hFb : ∀ i ω, ‖F i ω‖≤C) (f : Fin 3 → ℝ →ᵇ ℝ) (hf : ∀ j, UniformContinuous (f j))
    (hc : ∀ j ε, 0<ε → Tendsto (fun i => (μ i).real {ω | ε≤|X j i ω-Y j i ω|}) atTop (𝓝 0)) :
    Tendsto (fun i => ∫ ω, F i ω*(f 0 (X 0 i ω)*f 1 (X 1 i ω)*f 2 (X 2 i ω)-
      f 0 (Y 0 i ω)*f 1 (Y 1 i ω)*f 2 (Y 2 i ω)) ∂μ i) atTop (𝓝 0) := by
  have h1 := weighted_product_test_perturbation μ (X 0) (Y 0) (X 1) (Y 1)
    (hX 0) (hY 0) (hX 1) (hY 1) (fun i ω => F i ω*f 2 (X 2 i ω))
    (fun i => (hF i).mul ((f 2).continuous.measurable.comp (hX 2 i)))
    (C*‖f 2‖) (by positivity) (fun i ω => by
      rw [norm_mul]
      exact mul_le_mul (hFb i ω) ((f 2).norm_coe_le_norm _) (norm_nonneg _) hC)
    (f 0) (f 1) (hf 0) (hf 1) (hc 0) (hc 1)
  have h2 := weighted_test_perturbation μ (X 2) (Y 2) (hX 2) (hY 2)
    (fun i ω => F i ω*(f 0 (Y 0 i ω)*f 1 (Y 1 i ω)))
    (fun i => (hF i).mul (((f 0).continuous.measurable.comp (hY 0 i)).mul
      ((f 1).continuous.measurable.comp (hY 1 i))))
    (C*(‖f 0‖*‖f 1‖)) (by positivity) (fun i ω => by
      simp only [norm_mul]
      exact mul_le_mul (hFb i ω) (mul_le_mul ((f 0).norm_coe_le_norm _)
        ((f 1).norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)) (by positivity) hC)
    (f 2) (hf 2) (hc 2)
  have hA (i) : Integrable (fun ω => F i ω*f 2 (X 2 i ω)*
      (f 0 (X 0 i ω)*f 1 (X 1 i ω)-f 0 (Y 0 i ω)*f 1 (Y 1 i ω))) (μ i) := by
    apply Integrable.of_bound (((hF i).mul ((f 2).continuous.measurable.comp (hX 2 i))).mul
      ((((f 0).continuous.measurable.comp (hX 0 i)).mul ((f 1).continuous.measurable.comp (hX 1 i))).sub
      (((f 0).continuous.measurable.comp (hY 0 i)).mul ((f 1).continuous.measurable.comp (hY 1 i))))).aestronglyMeasurable
      ((C*‖f 2‖)*(2*(‖f 0‖*‖f 1‖)))
    apply ae_of_all
    intro ω
    change ‖F i ω*f 2 (X 2 i ω)*(f 0 (X 0 i ω)*f 1 (X 1 i ω)-f 0 (Y 0 i ω)*f 1 (Y 1 i ω))‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
    · rw [norm_mul]; exact mul_le_mul (hFb i ω) ((f 2).norm_coe_le_norm _) (norm_nonneg _) hC
    · apply (norm_sub_le _ _).trans
      simp only [norm_mul]
      have hb (Z : Fin 3 → ℕ → Ω → ℝ) := mul_le_mul ((f 0).norm_coe_le_norm (Z 0 i ω))
        ((f 1).norm_coe_le_norm (Z 1 i ω)) (norm_nonneg _) (norm_nonneg _)
      linarith [hb X,hb Y]
  have hB (i) : Integrable (fun ω => F i ω*(f 0 (Y 0 i ω)*f 1 (Y 1 i ω))*
      (f 2 (X 2 i ω)-f 2 (Y 2 i ω))) (μ i) := by
    apply Integrable.of_bound (((hF i).mul (((f 0).continuous.measurable.comp (hY 0 i)).mul
      ((f 1).continuous.measurable.comp (hY 1 i)))).mul
      (((f 2).continuous.measurable.comp (hX 2 i)).sub ((f 2).continuous.measurable.comp (hY 2 i)))).aestronglyMeasurable
      ((C*(‖f 0‖*‖f 1‖))*(2*‖f 2‖))
    apply ae_of_all
    intro ω
    change ‖F i ω*(f 0 (Y 0 i ω)*f 1 (Y 1 i ω))*(f 2 (X 2 i ω)-f 2 (Y 2 i ω))‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
    · simp only [norm_mul]
      exact mul_le_mul (hFb i ω) (mul_le_mul ((f 0).norm_coe_le_norm _)
        ((f 1).norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)) (by positivity) hC
    · exact (norm_sub_le _ _).trans (by
        linarith [(f 2).norm_coe_le_norm (X 2 i ω), (f 2).norm_coe_le_norm (Y 2 i ω)])
  have hs := h1.add h2
  simp only [add_zero] at hs
  apply hs.congr
  intro i
  rw [← integral_add (hA i) (hB i)]
  congr 1
  funext ω
  ring

end DirectionalTransience

end

section

open MeasureTheory Filter
namespace DirectionalTransience

lemma integrable_bounded_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (C D : ℝ) (hC : 0≤C) (hFb : ∀ ω, ‖F ω‖≤C) (hGb : ∀ ω, ‖G ω‖≤D) :
    Integrable (fun ω => F ω*G ω) μ :=
  Integrable.of_bound (hF.mul hG).aestronglyMeasurable (C*D) (ae_of_all _ fun ω => by
    rw [norm_mul]; exact mul_le_mul (hFb ω) (hGb ω) (norm_nonneg _) hC)

lemma integral_weighted_sub_bounded {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G K : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (hK : Measurable K)
    (C D : ℝ) (hC : 0≤C) (hFb : ∀ ω, ‖F ω‖≤C) (hGb : ∀ ω, ‖G ω‖≤D) (hKb : ∀ ω, ‖K ω‖≤D) :
    (∫ ω, F ω*(G ω-K ω) ∂μ) = (∫ ω, F ω*G ω ∂μ)-(∫ ω, F ω*K ω ∂μ) := by
  simp_rw [mul_sub]
  exact integral_sub (integrable_bounded_mul μ F G hF hG C D hC hFb hGb)
    (integrable_bounded_mul μ F K hF hK C D hC hFb hKb)

end DirectionalTransience

end

end

end OAI

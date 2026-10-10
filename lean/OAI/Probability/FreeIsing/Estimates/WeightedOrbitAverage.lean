import OAI.Probability.FreeIsing.Estimates.DependentWeight

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.WeightedOrbitAverage

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_weight_mul_comp
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (weight F : Ω → ℝ) (hw : ∀ᵐ ω ∂μ, weight (T ω) = weight ω) :
    (∫ ω, weight ω * F (T ω) ∂μ) = ∫ ω, weight ω * F ω ∂μ := by
  calc
    (∫ ω, weight ω * F (T ω) ∂μ) =
        ∫ ω, weight (T ω) * F (T ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hw] with ω hω
      rw [hω]
    _ = ∫ ω, weight ω * F ω ∂μ :=
      hT.integral_comp T.measurableEmbedding (fun ω => weight ω * F ω)

theorem integrable_weight_mul_comp
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (weight F : Ω → ℝ) (hw : ∀ᵐ ω ∂μ, weight (T ω) = weight ω)
    (hF : Integrable (fun ω => weight ω * F ω) μ) :
    Integrable (fun ω => weight ω * F (T ω)) μ := by
  apply ((hT.integrable_comp hF.aestronglyMeasurable).2 hF).congr
  filter_upwards [hw] with ω hω
  simp only [Function.comp_def, hω]

def average [Fintype ι] (F : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, F i ω

theorem integral_weight_mul_average [Fintype ι]
    (weight : Ω → ℝ) (F : ι → Ω → ℝ)
    (hF : ∀ i, Integrable (fun ω => weight ω * F i ω) μ) :
    (∫ ω, weight ω * average F ω ∂μ) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ ω, weight ω * F i ω ∂μ := by
  have heq : (fun ω => weight ω * average F ω) =
      fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, weight ω * F i ω := by
    funext ω
    simp only [average, ← Finset.mul_sum]
    ring
  rw [heq, integral_const_mul, integral_finsetSum _ (fun i _ => hF i)]

theorem integral_weight_mul_orbit_average [Fintype ι] [Nonempty ι]
    (T : ι → Ω ≃ᵐ Ω) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (weight F : Ω → ℝ)
    (hw : ∀ i, ∀ᵐ ω ∂μ, weight (T i ω) = weight ω)
    (hF : Integrable (fun ω => weight ω * F ω) μ) :
    (∫ ω, weight ω * average (fun i ω => F (T i ω)) ω ∂μ) =
      ∫ ω, weight ω * F ω ∂μ := by
  rw [integral_weight_mul_average weight _
    (fun i => integrable_weight_mul_comp (T i) (hT i) weight F (hw i) hF)]
  simp only [integral_weight_mul_comp (T _) (hT _) weight F (hw _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem integrable_weight_mul_average [Fintype ι]
    (weight : Ω → ℝ) (F : ι → Ω → ℝ)
    (hF : ∀ i, Integrable (fun ω => weight ω * F i ω) μ) :
    Integrable (fun ω => weight ω * average F ω) μ := by
  have hsum := (integrable_finsetSum Finset.univ (fun i _ => hF i)).const_mul
    (Fintype.card ι : ℝ)⁻¹
  convert hsum using 1
  funext ω
  simp only [average, ← Finset.mul_sum]
  ring

theorem integral_weight_mul_le_average [Fintype ι] [Nonempty ι]
    (T : ι → Ω ≃ᵐ Ω) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (weight F : Ω → ℝ) (G : ι → Ω → ℝ)
    (hw : ∀ i, ∀ᵐ ω ∂μ, weight (T i ω) = weight ω)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ weight ω)
    (hF : Integrable (fun ω => weight ω * F ω) μ)
    (hG : ∀ i, Integrable (fun ω => weight ω * G i ω) μ)
    (hFG : ∀ i, ∀ᵐ ω ∂μ, F (T i ω) ≤ G i ω) :
    (∫ ω, weight ω * F ω ∂μ) ≤ ∫ ω, weight ω * average G ω ∂μ := by
  rw [← integral_weight_mul_orbit_average T hT weight F hw hF,
    integral_weight_mul_average weight _
      (fun i => integrable_weight_mul_comp (T i) (hT i) weight F (hw i) hF),
    integral_weight_mul_average weight G hG]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro i _
  apply integral_mono_ae
    (integrable_weight_mul_comp (T i) (hT i) weight F (hw i) hF) (hG i)
  filter_upwards [hw0, hFG i] with ω hω0 hω
  exact mul_le_mul_of_nonneg_left hω hω0

theorem integral_weight_mul_le_of_average_tail [Fintype ι] [Nonempty ι]
    [IsFiniteMeasure μ]
    (T : ι → Ω ≃ᵐ Ω) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (weight F : Ω → ℝ) (G : ι → Ω → ℝ) {a M ε : ℝ}
    (hw : ∀ i, ∀ᵐ ω ∂μ, weight (T i ω) = weight ω)
    (hweight : Integrable weight μ)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ weight ω)
    (hwM : ∀ᵐ ω ∂μ, weight ω ≤ M)
    (hF : Integrable (fun ω => weight ω * F ω) μ)
    (hG : ∀ i, Integrable (fun ω => weight ω * G i ω) μ)
    (hFG : ∀ i, ∀ᵐ ω ∂μ, F (T i ω) ≤ G i ω)
    (hmeas : Measurable (average G))
    (hG0 : ∀ᵐ ω ∂μ, 0 ≤ average G ω)
    (hG1 : ∀ᵐ ω ∂μ, average G ω ≤ 1)
    (ha : 0 ≤ a) (hM : 0 ≤ M)
    (htail : μ.real {ω | a < average G ω} ≤ ε) :
    (∫ ω, weight ω * F ω ∂μ) ≤ a * (∫ ω, weight ω ∂μ) + M * ε := by
  exact (integral_weight_mul_le_average T hT weight F G hw hw0 hF hG hFG).trans
    (DependentWeight.integral_mul_le_of_tail_probability hweight hmeas ha hM
      hw0 hwM hG0 hG1 htail)

end Problem367.WeightedOrbitAverage

end

end OAI

import OAI.Probability.FreeIsing.Conditioning.CovarianceLimit
import OAI.Probability.FreeIsing.Estimates.ContinuousModification

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.ObservationStepApproximation

open ContinuousModification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem tendsto_integral_sq_dyadic_sample
    (ν : Measure ℝ) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {F : ℝ → Ω → ℝ}
    (hF : Measurable (Function.uncurry F))
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t => F t ω))
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖F t ω‖ ≤ R) :
    Tendsto (fun n => ∫ p : ℝ × Ω,
      (F (dyadicLeft p.1 n) p.2 - F p.1 p.2) ^ 2 ∂ν.prod μ) atTop (𝓝 0) := by
  have hFt (t : ℝ) : Measurable (F t) :=
    hF.comp (measurable_const.prodMk measurable_id)
  apply tendsto_integral_prod_sq_sub_of_bounded_ae ν μ
    (measurable_dyadic_sample hFt) hF hR
  · exact fun n => Filter.Eventually.of_forall (fun t => hbound (dyadicLeft t n))
  · exact Filter.Eventually.of_forall hbound
  · apply Filter.Eventually.of_forall
    intro t
    filter_upwards [hcont] with ω hω
    exact (hω.tendsto t).comp (tendsto_dyadicLeft t)

theorem tendsto_integral_sq_dyadic_sample_of_continuous
    (ν : Measure ℝ) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {F : ℝ → Ω → ℝ}
    (hF : ∀ t, Measurable (F t)) (hcont : ∀ ω, Continuous (fun t => F t ω))
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ t, ∀ᵐ ω ∂μ, ‖F t ω‖ ≤ R) :
    Tendsto (fun n => ∫ p : ℝ × Ω,
      (F (dyadicLeft p.1 n) p.2 - F p.1 p.2) ^ 2 ∂ν.prod μ) atTop (𝓝 0) :=
  tendsto_integral_sq_dyadic_sample ν μ
    (measurable_uncurry_of_continuous_of_measurable hcont hF)
    (Filter.Eventually.of_forall hcont) hR hbound

theorem stronglyProgressive_dyadic_sample (Flt : Filtration ℝ mΩ)
    {F : ℝ → Ω → ℝ} (hF : Adapted Flt F) (n : ℕ) :
    IsStronglyProgressive Flt (fun t ω => F (dyadicLeft t n) ω) :=
  (isProgressive_dyadic_sample Flt hF n).isStronglyProgressive

theorem tendsto_integral_sq_dyadic_observable
    {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure ℝ) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (X : ℝ → Ω → E) (M : E → ℝ)
    (hX : ∀ t, Measurable (X t)) (hXcont : ∀ ω, Continuous (fun t => X t ω))
    (hM : Continuous M) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ x, ‖M x‖ ≤ R) :
    Tendsto (fun n => ∫ p : ℝ × Ω,
      (M (X (dyadicLeft p.1 n) p.2) - M (X p.1 p.2)) ^ 2 ∂ν.prod μ)
      atTop (𝓝 0) := by
  apply tendsto_integral_sq_dyadic_sample_of_continuous ν μ
    (fun t => hM.measurable.comp (hX t)) (fun ω => hM.comp (hXcont ω)) hR
  exact fun t => Filter.Eventually.of_forall (fun ω => hbound (X t ω))

theorem finite_dyadicLeft_image_Icc (a b : ℝ) (n : ℕ) :
    ((fun t => dyadicLeft t n) '' Set.Icc a b).Finite := by
  let I : Set ℤ := Set.Icc ⌊(2 : ℝ)^n * a⌋ ⌊(2 : ℝ)^n * b⌋
  apply ((Set.finite_Icc _ _).image (fun k : ℤ => (k : ℝ) / (2 : ℝ)^n)).subset
  rintro y ⟨t, ht, rfl⟩
  refine ⟨⌊(2 : ℝ)^n * t⌋, ?_, rfl⟩
  exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left ht.1 (by positivity)),
    Int.floor_mono (mul_le_mul_of_nonneg_left ht.2 (by positivity))⟩

theorem dyadicLeft_eq_on_cell (n : ℕ) (k : ℤ) {t : ℝ}
    (ht : t ∈ Set.Ico ((k : ℝ) / (2 : ℝ)^n) (((k : ℝ) + 1) / (2 : ℝ)^n)) :
    dyadicLeft t n = (k : ℝ) / (2 : ℝ)^n := by
  have hpos : 0 < (2 : ℝ)^n := by positivity
  have hlo := (div_le_iff₀ hpos).mp ht.1
  have hhi := (lt_div_iff₀ hpos).mp ht.2
  have hfloor : ⌊(2 : ℝ)^n * t⌋ = k :=
    Int.floor_eq_iff.mpr ⟨by nlinarith, by nlinarith⟩
  simp only [dyadicLeft, hfloor]

theorem dyadic_coefficient_stronglyMeasurable
    (Flt : Filtration ℝ mΩ) {F : ℝ → Ω → ℝ} (hF : StronglyAdapted Flt F)
    (n : ℕ) (k : ℤ) :
    StronglyMeasurable[Flt ((k : ℝ) / (2 : ℝ)^n)]
      (F ((k : ℝ) / (2 : ℝ)^n)) := hF _

theorem exists_diagonal_meanSquare
    (μ : Measure Ω) {X : ℕ → ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ} {Z : Ω → ℝ}
    (hX : ∀ n k, MemLp (X n k) 2 μ) (hY : ∀ n, MemLp (Y n) 2 μ)
    (hZ : MemLp Z 2 μ)
    (hXY : ∀ n, Tendsto (fun k => ∫ ω, (X n k ω - Y n ω) ^ 2 ∂μ) atTop (𝓝 0))
    (hYZ : Tendsto (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧
      Tendsto (fun n => ∫ ω, (X n (k n) ω - Z ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  have hex (n : ℕ) : ∃ k, n ≤ k ∧
      (∫ ω, (X n k ω - Y n ω) ^ 2 ∂μ) < 1 / ((n : ℝ) + 1) := by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ((eventually_ge_atTop n).and ((hXY n).eventually (gt_mem_nhds hpos))).exists
  choose k hk herror using hex
  refine ⟨k, hk, ?_⟩
  have hupper (n : ℕ) :
      (∫ ω, (X n (k n) ω - Z ω) ^ 2 ∂μ) ≤
        2 * (1 / ((n : ℝ) + 1)) + 2 * ∫ ω, (Y n ω - Z ω) ^ 2 ∂μ := by
    have hA : Integrable (fun ω => (X n (k n) ω - Y n ω) ^ 2) μ :=
      ((hX n (k n)).sub (hY n)).integrable_sq
    have hB : Integrable (fun ω => (Y n ω - Z ω) ^ 2) μ :=
      ((hY n).sub hZ).integrable_sq
    have hC : Integrable (fun ω => (X n (k n) ω - Z ω) ^ 2) μ :=
      ((hX n (k n)).sub hZ).integrable_sq
    calc
      (∫ ω, (X n (k n) ω - Z ω) ^ 2 ∂μ) ≤
          ∫ ω, 2 * (X n (k n) ω - Y n ω) ^ 2 + 2 * (Y n ω - Z ω) ^ 2 ∂μ := by
        apply integral_mono hC ((hA.const_mul 2).add (hB.const_mul 2))
        intro ω
        change (X n (k n) ω - Z ω) ^ 2 ≤
          2 * (X n (k n) ω - Y n ω) ^ 2 + 2 * (Y n ω - Z ω) ^ 2
        nlinarith [sq_nonneg (X n (k n) ω - 2 * Y n ω + Z ω)]
      _ = 2 * (∫ ω, (X n (k n) ω - Y n ω) ^ 2 ∂μ) +
          2 * ∫ ω, (Y n ω - Z ω) ^ 2 ∂μ := by
        rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul,
          integral_const_mul]
      _ ≤ _ := by linarith [herror n]
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1)) +
      2 * ∫ ω, (Y n ω - Z ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).add
      (hYZ.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => integral_nonneg (fun ω => sq_nonneg _)) hupper

theorem exists_dyadic_diagonal_meanSquare
    (ν : Measure ℝ) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {F : ℕ → ℝ → Ω → ℝ} {Z : ℝ × Ω → ℝ}
    (hF : ∀ n, Measurable (Function.uncurry (F n))) (hZ : Measurable Z)
    (hcont : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => F n t ω))
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ n t ω, ‖F n t ω‖ ≤ R)
    (hZbound : ∀ᵐ p ∂ν.prod μ, ‖Z p‖ ≤ R)
    (hlimit : Tendsto (fun n => ∫ p : ℝ × Ω,
      (F n p.1 p.2 - Z p) ^ 2 ∂ν.prod μ) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧
      Tendsto (fun n => ∫ p : ℝ × Ω,
        (F n (dyadicLeft p.1 (k n)) p.2 - Z p) ^ 2 ∂ν.prod μ) atTop (𝓝 0) := by
  have hFt (n : ℕ) (t : ℝ) : Measurable (F n t) :=
    (hF n).comp (measurable_const.prodMk measurable_id)
  apply exists_diagonal_meanSquare (ν.prod μ)
    (X := fun n k p => F n (dyadicLeft p.1 k) p.2)
    (Y := fun n p => F n p.1 p.2) (Z := Z)
  · intro n k
    apply (memLp_const R).mono'
      ((measurable_dyadic_sample (hFt n) k).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun p => hbound n (dyadicLeft p.1 k) p.2)
  · intro n
    exact (memLp_const R).mono' (hF n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound n p.1 p.2))
  · exact (memLp_const R).mono' hZ.aestronglyMeasurable hZbound
  · intro n
    exact tendsto_integral_sq_dyadic_sample ν μ (hF n) (hcont n) hR
      (fun t => Filter.Eventually.of_forall (fun ω => hbound n t ω))
  · exact hlimit

end Problem367.ObservationStepApproximation

end

end OAI

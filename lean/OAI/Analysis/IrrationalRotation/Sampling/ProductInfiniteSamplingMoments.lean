import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingMoments
import OAI.Analysis.IrrationalRotation.Sampling.SamplingAlmostSure
import Mathlib.Probability.ProductMeasure

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Invariant233.ProductSampling

theorem measurePreserving_finset_restrict
    {κ : Type*} {X : κ → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : κ) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (D : Finset κ) :
    MeasurePreserving D.restrict (Measure.infinitePi μ)
      (Measure.pi (fun i : D => μ i)) :=
  ⟨by fun_prop, Measure.infinitePi_map_restrict μ⟩

theorem integral_integral_finset_restrict
    {κ α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (D : Finset κ) (F : (D → α) → (D → β) → ℝ)
    (hF : Integrable (fun p : (D → α) × (D → β) => F p.1 p.2)
      ((Measure.pi (fun i : D => μ i)).prod (Measure.pi (fun i : D => ν i)))) :
    (∫ a, ∫ b, F (D.restrict a) (D.restrict b)
      ∂Measure.infinitePi ν ∂Measure.infinitePi μ) =
      ∫ a, ∫ b, F a b ∂Measure.pi (fun i : D => ν i)
        ∂Measure.pi (fun i : D => μ i) := by
  let r : (κ → α) × (κ → β) → (D → α) × (D → β) :=
    Prod.map D.restrict D.restrict
  have hr : MeasurePreserving r
      ((Measure.infinitePi μ).prod (Measure.infinitePi ν))
      ((Measure.pi (fun i : D => μ i)).prod (Measure.pi (fun i : D => ν i))) :=
    (measurePreserving_finset_restrict μ D).prod
      (measurePreserving_finset_restrict ν D)
  have hi : Integrable (fun p : (κ → α) × (κ → β) =>
      F (D.restrict p.1) (D.restrict p.2))
      ((Measure.infinitePi μ).prod (Measure.infinitePi ν)) :=
    hr.integrable_comp_of_integrable hF
  rw [← integral_prod _ hi, ← integral_prod _ hF]
  have hm : AEStronglyMeasurable (fun p : (D → α) × (D → β) => F p.1 p.2)
      (Measure.map r ((Measure.infinitePi μ).prod (Measure.infinitePi ν))) := by
    rw [hr.map_eq]
    exact hF.aestronglyMeasurable
  simpa [hr.map_eq, r] using
    (integral_map hr.measurable.aemeasurable hm).symm

theorem integrable_average_coordinate_error_sq
    {κ ι α β : Type*} [Fintype κ] [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (s : Finset ι) (v : ι → κ → α → β → ℝ) (z : κ → β → ℝ)
    (hv : ∀ n i, MemLp (fun p : α × β => v n i p.1 p.2) 2 ((μ i).prod (ν i)))
    (hz : ∀ i, MemLp (z i) 2 (ν i)) :
    Integrable (fun p : (κ → α) × (κ → β) =>
      ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (p.1 i) (p.2 i)) -
        ∏ i, z i (p.2 i)) ^ 2) ((Measure.pi μ).prod (Measure.pi ν)) := by
  let V : ι → κ → α × β → ℝ := fun n i p => v n i p.1 p.2
  let Z : κ → α × β → ℝ := fun i p => z i p.2
  have hZ (i : κ) : MemLp (Z i) 2 ((μ i).prod (ν i)) := (hz i).comp_snd (μ i)
  have hi :=
    (InvariantRotation.SamplingMomentBounds.memLp_average_coordinate_products
      s V Z hv hZ).integrable_sq
  let e := MeasurableEquiv.arrowProdEquivProdArrow α β κ
  have he := measurePreserving_arrowProdEquivProdArrow α β κ μ ν
  exact (he.integrable_comp_emb e.measurableEmbedding).mp hi

theorem expected_integral_infinite_average_products_sub_sq_le
    {κ ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : κ → Measure α) (ν : κ → Measure β)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (D : Finset κ) (s : Finset ι) (hs : s.Nonempty)
    (v : ι → D → α → β → ℝ) (z : D → β → ℝ)
    (hv : ∀ n i, MemLp (fun p : α × β => v n i p.1 p.2) 2 ((μ i).prod (ν i)))
    (hz : ∀ i, MemLp (z i) 2 (ν i))
    {B T ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i : D, (∫ x, (z i x) ^ 2 ∂ν i) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i : D,
      (∫ p : α × β, (v n i p.1 p.2) ^ 2 ∂(μ i).prod (ν i)) ≤ T)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i : D,
      |(∫ p : α × β, v n i p.1 p.2 * v m i p.1 p.2 ∂(μ i).prod (ν i)) -
        (∫ x, (z i x) ^ 2 ∂ν i)| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i : D,
      |(∫ p : α × β, v n i p.1 p.2 * z i p.2 ∂(μ i).prod (ν i)) -
        (∫ x, (z i x) ^ 2 ∂ν i)| ≤ ε) :
    (∫ a : κ → α, ∫ b : κ → β,
      ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i : D, v n i (a i) (b i)) -
        ∏ i : D, z i (b i)) ^ 2 ∂Measure.infinitePi ν ∂Measure.infinitePi μ) ≤
      T ^ D.card / (s.card : ℝ) +
        3 * ((D.card : ℝ) * ε * (B + ε) ^ (D.card - 1)) := by
  let F : (D → α) → (D → β) → ℝ := fun a b =>
    ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (a i) (b i)) -
      ∏ i, z i (b i)) ^ 2
  have hi := integrable_average_coordinate_error_sq
    (fun i : D => μ i) (fun i : D => ν i) s v z hv hz
  have heq := integral_integral_finset_restrict μ ν D F hi
  change (∫ a, ∫ b, F (D.restrict a) (D.restrict b)
    ∂Measure.infinitePi ν ∂Measure.infinitePi μ) ≤ _
  rw [heq]
  simpa only [Fintype.card_coe] using
    InvariantRotation.SamplingMomentBounds.expected_integral_average_products_sub_sq_le
      (fun i : D => μ i) (fun i : D => ν i) s hs v z hv hz hB hε
      hbase hdiag hoff hcross

theorem ae_summable_spatial_integral_sq_of_summable_bound
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ℕ → Ω → X → ℝ) (b : ℕ → ℝ)
    (hsq : ∀ n, Integrable (fun p : Ω × X => (F n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ n, (∫ a, ∫ x, (F n a x) ^ 2 ∂ν ∂μ) ≤ b n)
    (hb : Summable b) :
    ∀ᵐ a ∂μ, Summable (fun n => ∫ x, (F n a x) ^ 2 ∂ν) := by
  let e : ℕ → Ω → ℝ := fun n a => ∫ x, (F n a x) ^ 2 ∂ν
  have he : ∀ n a, 0 ≤ e n a := fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  have hi : ∀ n, Integrable (e n) μ := fun n => (hsq n).integral_prod_left
  have hlin : ∀ n, (∫⁻ a, ENNReal.ofReal (e n a) ∂μ) ≤ ENNReal.ofReal (b n) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall (he n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact ae_summable_of_lintegral_tsum_ne_top he
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hlin) hb.tsum_ofReal_ne_top.lt_top))

theorem ae_memLp_and_tendsto_norm_of_summable_expected_sq
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ℕ → Ω → X → ℝ) (b : ℕ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (fun p : Ω × X => F n p.1 p.2) (μ.prod ν))
    (hsq : ∀ n, Integrable (fun p : Ω × X => (F n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ n, (∫ a, ∫ x, (F n a x) ^ 2 ∂ν ∂μ) ≤ b n)
    (hb : Summable b) :
    ∀ᵐ a ∂μ, ∃ hf : ∀ n, MemLp (F n a) 2 ν,
      Summable (fun n => ∫ x, (F n a x) ^ 2 ∂ν) ∧
      Tendsto (fun n => ‖(hf n).toLp (F n a)‖) atTop (𝓝 0) := by
  have hm : ∀ᵐ a ∂μ, ∀ n, MemLp (F n a) 2 ν := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [(hmeas n).prodMk_left, (hsq n).prod_right_ae] with a ha hia
    exact (memLp_two_iff_integrable_sq ha).mpr hia
  filter_upwards [hm, ae_summable_spatial_integral_sq_of_summable_bound F b hsq hbound hb]
    with a ha hsum
  refine ⟨ha, hsum, ?_⟩
  have hnorm (n : ℕ) :
      Real.sqrt (∫ x, (F n a x) ^ 2 ∂ν) = ‖(ha n).toLp (F n a)‖ := by
    have heq : ‖(ha n).toLp (F n a)‖ ^ 2 = ∫ x, (F n a x) ^ 2 ∂ν := by
      rw [InvariantRotation.SamplingMomentBounds.l2_norm_sq_eq_integral_sq]
      apply integral_congr_ae
      filter_upwards [(ha n).coeFn_toLp] with x hx
      rw [hx]
    rw [← heq, Real.sqrt_sq (norm_nonneg _)]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsum.tendsto_atTop_zero
  simpa only [Function.comp_def, hnorm, Real.sqrt_zero] using h

theorem ae_all_memLp_and_tendsto_norm_of_summable_expected_sq
    {ι Ω X : Type*} [Countable ι] [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ι → ℕ → Ω → X → ℝ) (b : ι → ℕ → ℝ)
    (hmeas : ∀ i n, AEStronglyMeasurable (fun p : Ω × X => F i n p.1 p.2) (μ.prod ν))
    (hsq : ∀ i n, Integrable (fun p : Ω × X => (F i n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ i n, (∫ a, ∫ x, (F i n a x) ^ 2 ∂ν ∂μ) ≤ b i n)
    (hb : ∀ i, Summable (b i)) :
    ∀ᵐ a ∂μ, ∀ i, ∃ hf : ∀ n, MemLp (F i n a) 2 ν,
      Summable (fun n => ∫ x, (F i n a x) ^ 2 ∂ν) ∧
      Tendsto (fun n => ‖(hf n).toLp (F i n a)‖) atTop (𝓝 0) := by
  exact ae_all_iff.mpr fun i =>
    ae_memLp_and_tendsto_norm_of_summable_expected_sq
      (F i) (b i) (hmeas i) (hsq i) (hbound i) (hb i)

end Invariant233.ProductSampling

namespace Invariant233.ProductSampling

theorem ae_memLp_and_tendsto_norm_of_eventually_expected_sq
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ℕ → Ω → X → ℝ) (b : ℕ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (fun p : Ω × X => F n p.1 p.2) (μ.prod ν))
    (hsq : ∀ n, Integrable (fun p : Ω × X => (F n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ᶠ n in atTop, (∫ a, ∫ x, (F n a x) ^ 2 ∂ν ∂μ) ≤ b n)
    (hb : Summable b) :
    ∀ᵐ a ∂μ, ∃ hf : ∀ n, MemLp (F n a) 2 ν,
      Summable (fun n => ∫ x, (F n a x) ^ 2 ∂ν) ∧
      Tendsto (fun n => ‖(hf n).toLp (F n a)‖) atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun n => ∫ a, ∫ x, (F n a x) ^ 2 ∂ν ∂μ
  have he : Summable e := by
    apply hb.of_norm_bounded_eventually_nat
    filter_upwards [hbound] with n hn
    have hnonneg : 0 ≤ e n := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
    simpa only [Real.norm_of_nonneg hnonneg] using hn
  exact ae_memLp_and_tendsto_norm_of_summable_expected_sq
    F e hmeas hsq (fun _ => le_rfl) he

theorem ae_all_memLp_and_tendsto_norm_of_eventually_expected_sq
    {ι Ω X : Type*} [Countable ι] [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ι → ℕ → Ω → X → ℝ) (b : ι → ℕ → ℝ)
    (hmeas : ∀ i n, AEStronglyMeasurable (fun p : Ω × X => F i n p.1 p.2) (μ.prod ν))
    (hsq : ∀ i n, Integrable (fun p : Ω × X => (F i n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ i, ∀ᶠ n in atTop, (∫ a, ∫ x, (F i n a x) ^ 2 ∂ν ∂μ) ≤ b i n)
    (hb : ∀ i, Summable (b i)) :
    ∀ᵐ a ∂μ, ∀ i, ∃ hf : ∀ n, MemLp (F i n a) 2 ν,
      Summable (fun n => ∫ x, (F i n a x) ^ 2 ∂ν) ∧
      Tendsto (fun n => ‖(hf n).toLp (F i n a)‖) atTop (𝓝 0) := by
  exact ae_all_iff.mpr fun i =>
    ae_memLp_and_tendsto_norm_of_eventually_expected_sq
      (F i) (b i) (hmeas i) (hsq i) (hbound i) (hb i)

end Invariant233.ProductSampling

end

end OAI

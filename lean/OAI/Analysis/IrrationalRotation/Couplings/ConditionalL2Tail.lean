import OAI.Analysis.IrrationalRotation.Couplings.ConditionalMaskedTail
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

open MeasureTheory
open scoped ENNReal lp

namespace InvariantProjection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem l2_tsum_ofReal_sq (x : ℓ²(ℤ, ℂ)) :
    (∑' i : ℤ, ENNReal.ofReal (‖x i‖ ^ 2)) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hs : HasSum (fun i : ℤ => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
    simpa using lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]

theorem lintegral_l2_sq_le_one [IsProbabilityMeasure μ]
    (ξ : Ω → ℓ²(ℤ, ℂ)) (hξ : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) :
    (∫⁻ ω, ∑' i : ℤ, ENNReal.ofReal (‖ξ ω i‖ ^ 2) ∂μ) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hξ] with ω hω
      rw [l2_tsum_ofReal_sq]
      apply ENNReal.ofReal_le_one.mpr
      nlinarith [norm_nonneg (ξ ω)]
    _ = 1 := by simp

theorem lintegral_l2_masked_tail_le_of_condExp
    [IsProbabilityMeasure μ]
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (hγ : StronglyMeasurable γ)
    (hξ_ball : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) (hγ_ball : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1)
    (e : ℤ ≃ ℤ) {H : Set (Ω × ℤ)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hξ : StronglyMeasurable[m] ξ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcond : ∀ i : ℤ, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ) :
    (∫⁻ ω, ∑' i : ℤ, H.indicator
      (fun z => ENNReal.ofReal ‖ξ z.1 z.2‖ * ENNReal.ofReal ‖γ z.1 (e z.2)‖)
      (ω, i) ∂μ) ≤ ENNReal.ofReal (Real.sqrt δ) := by
  let : MeasurableSpace Ω := mΩ
  have hxcoord (i : ℤ) : StronglyMeasurable[m] (fun ω => ξ ω i) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_stronglyMeasurable hξ
  have hycoord (i : ℤ) : StronglyMeasurable (fun ω => γ ω (e i)) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e i)).continuous.comp_stronglyMeasurable hγ
  apply lintegral_tsum_masked_mul_le_of_condExp
    (a := fun z : Ω × ℤ => ‖ξ z.1 z.2‖)
    (b := fun z : Ω × ℤ => ‖γ z.1 (e z.2)‖)
    (measurable_from_prod_countable_left fun i => ((hxcoord i).mono hm).norm.measurable)
    (measurable_from_prod_countable_left fun i => (hycoord i).norm.measurable)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hH hm hδ
    (fun i => (hxcoord i).norm.pow 2) hcond
  · exact lintegral_l2_sq_le_one ξ hξ_ball
  · have h := lintegral_l2_sq_le_one γ hγ_ball
    calc
      _ = ∫⁻ ω, ∑' i : ℤ, ENNReal.ofReal (‖γ ω i‖ ^ 2) ∂μ := by
        apply lintegral_congr
        intro ω
        exact e.tsum_eq (fun i => ENNReal.ofReal (‖γ ω i‖ ^ 2))
      _ ≤ 1 := h

theorem integral_l2_masked_tail_le_of_condExp
    [IsProbabilityMeasure μ]
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (hγ : StronglyMeasurable γ)
    (hξ_ball : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) (hγ_ball : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1)
    (e : ℤ ≃ ℤ) {H : Set (Ω × ℤ)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hξ : StronglyMeasurable[m] ξ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcond : ∀ i : ℤ, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ) :
    (∀ᵐ ω ∂μ, Summable (fun i : ℤ => H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i))) ∧
    Integrable (fun ω => ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) μ ∧
    (∫ ω, ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i) ∂μ) ≤ Real.sqrt δ := by
  let : MeasurableSpace Ω := mΩ
  have hbound := lintegral_l2_masked_tail_le_of_condExp
    (mΩ := mΩ) ξ γ hγ hξ_ball hγ_ball e hH hm hξ hδ hcond
  have hxcoord (i : ℤ) : StronglyMeasurable (fun ω => ξ ω i) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_stronglyMeasurable hξ).mono hm
  have hycoord (i : ℤ) : StronglyMeasurable (fun ω => γ ω (e i)) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e i)).continuous.comp_stronglyMeasurable hγ
  have hf (i : ℤ) : Measurable (fun ω => H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) := by
    have hs := hH.preimage (@measurable_prodMk_right Ω ℤ mΩ inferInstance i)
    convert (((hxcoord i).norm.measurable.mul (hycoord i).norm.measurable).indicator hs) using 1
    funext ω
    by_cases hi : (ω, i) ∈ H <;> simp [hi]
  apply Invariant233.MaskedTail.real_tsum_integrable_of_lintegral_bound hf
    (fun i ω => Set.indicator_nonneg (fun z _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (ω, i))
    (Real.sqrt_nonneg δ)
  convert hbound using 1
  apply lintegral_congr
  intro ω
  apply tsum_congr
  intro i
  by_cases hi : (ω, i) ∈ H
  · simp [hi, ENNReal.ofReal_mul (norm_nonneg _)]
  · simp [hi]

theorem integral_l2_masked_tail_le_of_condExp_right
    [IsProbabilityMeasure μ]
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (hξ : StronglyMeasurable ξ)
    (hξ_ball : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) (hγ_ball : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1)
    (e : ℤ ≃ ℤ) {H : Set (Ω × ℤ)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hγ : StronglyMeasurable[m] γ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcond : ∀ i : ℤ, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ) :
    Integrable (fun ω => ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) μ ∧
    (∫ ω, ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i) ∂μ) ≤ Real.sqrt δ := by
  let : MeasurableSpace Ω := mΩ
  let H' : Set (Ω × ℤ) := {z | (z.1, e.symm z.2) ∈ H}
  have hH' : MeasurableSet H' :=
    hH.preimage (measurable_fst.prodMk ((measurable_of_countable e.symm).comp measurable_snd))
  have hc' : ∀ j : ℤ, μ[({ω | (ω, j) ∈ H'}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ := fun j => hcond (e.symm j)
  have h := integral_l2_masked_tail_le_of_condExp (mΩ := mΩ)
    γ ξ hξ hγ_ball hξ_ball e.symm hH' hm hγ hδ hc'
  have heq : (fun ω => ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) =
      (fun ω => ∑' j : ℤ, H'.indicator
      (fun z => ‖γ z.1 z.2‖ * ‖ξ z.1 (e.symm z.2)‖) (ω, j)) := by
    funext ω
    rw [← e.tsum_eq (fun j => H'.indicator
      (fun z => ‖γ z.1 z.2‖ * ‖ξ z.1 (e.symm z.2)‖) (ω, j))]
    apply tsum_congr
    intro i
    by_cases hi : (ω, i) ∈ H <;> simp [H', hi, mul_comm]
  rw [heq]
  exact h.2

end InvariantProjection

end OAI

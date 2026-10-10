import OAI.Analysis.IrrationalRotation.Analysis.TaggedEventBounds
import OAI.Analysis.IrrationalRotation.Analysis.EndpointIntervalBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace InvariantRotation.TruncationEvent

open TaggedEventBounds EndpointIntervalBounds

variable {Ω : Type*} [MeasurableSpace Ω]

theorem currentBlock_mass_lower_bound (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : 0 ≤ 1 - (1 + 2 * (C * a)) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ x ∈ T i, X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    (1 - (1 + 2 * (C * a)) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
        ∀ i, X i (x i) < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i (x i)} := by
  let B₁ : Fin m → Set Ω := fun i => {x | 1 - a / (m : ℝ) ≤ X i x}
  let B₂ : Fin m → Set Ω := fun i => {x | Y i x ≤ a / (m : ℝ)}
  have hB₁ : ∀ i, MeasurableSet (B₁ i) := fun i =>
    measurableSet_le measurable_const (hX i)
  have hB₂ : ∀ i, MeasurableSet (B₂ i) := fun i =>
    measurableSet_le (hY i) measurable_const
  have hSafe' : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ := by
    intro i x hx
    exact ⟨not_le.mpr (hSafe i x hx).1, not_le.mpr (hSafe i x hx).2⟩
  have hd : 0 ≤ a / (m : ℝ) := div_nonneg ha (Nat.cast_nonneg m)
  have hBad₁ : ∀ i, (μ i).real (B₁ i) ≤ C * a / (m : ℝ) := by
    intro i
    simpa only [mul_div_assoc] using endpoint_function_upper_loss_le
      (μ i) (hX i) hC hd (hdomX i)
  have hBad₂ : ∀ i, (μ i).real (B₂ i) ≤ C * a / (m : ℝ) := by
    intro i
    simpa only [mul_div_assoc] using endpoint_function_lower_loss_le
      (μ i) (hY i) hC hd (hdomY i)
  have h := currentBlockEvent_measureReal_lower_bound m hm μ T B₁ B₂ hT hB₁ hB₂
    hSafe' hbudget hTag hBad₁ hBad₂
  simpa only [currentBlockEvent, B₁, B₂, Set.mem_ofPred_eq, not_le] using h

theorem currentBlock_mass_lower_bound_ae (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : 0 ≤ 1 - (1 + 2 * (C * a)) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ᵐ x ∂μ i, x ∈ T i →
      X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    (1 - (1 + 2 * (C * a)) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
        ∀ i, X i (x i) < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i (x i)} := by
  let T' : Fin m → Set Ω := fun i => T i ∩
    {x | X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x}
  have hT' : ∀ i, MeasurableSet (T' i) := fun i =>
    (hT i).inter ((measurableSet_lt (hX i) measurable_const).inter
      (measurableSet_lt measurable_const (hY i)))
  have hTag' : ∀ i, (μ i).real (T' i) = 1 / (m : ℝ) := by
    intro i
    have hae : T' i =ᵐ[μ i] T i := by
      filter_upwards [hSafe i] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
    exact (measureReal_congr hae).trans (hTag i)
  have h := currentBlock_mass_lower_bound m hm μ T' hT' hX hY hC ha hbudget hTag'
    (fun i x hx => hx.2) hdomX hdomY
  refine h.trans (measureReal_mono ?_)
  intro x hx
  obtain ⟨⟨i, hi⟩, hgood⟩ := hx
  exact ⟨⟨i, hi.1⟩, hgood⟩

theorem circle_currentBlock_mass (m : ℕ) (hm : 200 ≤ m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ x ∈ T i, X i x < 1 - 3 / (m : ℝ) ∧ 3 / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1)) :
    Real.exp (-90) ≤ (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
      ∀ i, X i (x i) < 1 - 3 / (m : ℝ) ∧ 3 / (m : ℝ) < Y i (x i)} := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hbudget : 0 ≤ 1 - (1 + 2 * ((10 : ℝ) * 3)) / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hmpos).mpr (by linarith)
  have h := currentBlock_mass_lower_bound m (by omega) μ T hT hX hY
    (C := 10) (a := 3) (by norm_num) (by norm_num) hbudget hTag hSafe
    (by simpa using hdomX) (by simpa using hdomY)
  norm_num only [show (1 : ℝ) + 2 * (10 * 3) = 61 by norm_num] at h
  exact (circle_tag_bound m hm).trans h

theorem product_currentBlock_mass (m : ℕ) (hm : 100 ≤ m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ x ∈ T i, X i x < 1 - 2 / (m : ℝ) ∧ 2 / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ (10 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) 1)) :
    Real.exp (-82) ≤ (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
      ∀ i, X i (x i) < 1 - 2 / (m : ℝ) ∧ 2 / (m : ℝ) < Y i (x i)} := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hbudget : 0 ≤ 1 - (1 + 2 * ((10 : ℝ) * 2)) / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hmpos).mpr (by linarith)
  have h := currentBlock_mass_lower_bound m (by omega) μ T hT hX hY
    (C := 10) (a := 2) (by norm_num) (by norm_num) hbudget hTag hSafe
    (by simpa using hdomX) (by simpa using hdomY)
  norm_num only [show (1 : ℝ) + 2 * (10 * 2) = 41 by norm_num] at h
  exact (product_tag_bound m hm).trans h

end InvariantRotation.TruncationEvent

end OAI

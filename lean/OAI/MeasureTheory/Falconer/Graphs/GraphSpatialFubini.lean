import OAI.MeasureTheory.Falconer.Graphs.GraphActualTransport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem compact_finite_spatial_integrable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α) (μ : Measure β)
    [IsFiniteMeasure μ] {K : Set α} (hK : MeasurableSet K) (hfinite : ν K < ∞)
    {f : α × β → ℂ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p, ‖f p‖ ≤ C) (hsupp : ∀ p, f p ≠ 0 → p.1 ∈ K) :
    Integrable f (ν.prod μ) := by
  have hi : Integrable (K.indicator (fun _ : α => C)) ν :=
    (integrableOn_const hfinite.ne).integrable_indicator hK
  apply (hi.comp_fst μ).mono hf.aestronglyMeasurable
  filter_upwards with p
  by_cases hp : p.1 ∈ K
  · simpa only [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg hC] using hbound p
  · have hz : f p = 0 := by by_contra hn; exact hp (hsupp p hn)
    simp [indicator_of_notMem hp, hz]

theorem graphTransport_family_measurable {α : Type*} [MeasurableSpace α]
    (F : α → ℝ → UnitCircle → UnitCircle → ℂ)
    (hF : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × α =>
      F p.2 p.1.1 p.1.2.1 p.1.2.2)) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R axis : ℝ) :
    Measurable (fun p : (ℝ × Plane) × α => graphTransport (F p.2) Ψ R axis p.1) := by
  have ha : Measurable (fun p : (ℝ × Plane) × α => graphPlaneAngle p.1.2) :=
    graphPlaneAngle_measurable.comp (measurable_snd.comp measurable_fst)
  have hg : Measurable (fun p : (ℝ × Plane) × α =>
      F p.2 (R*(‖p.1.2‖*Real.sqrt (1+p.1.1^2)/2))
        (sourceUnitDirection (graphPlaneAngle p.1.2+Real.arctan p.1.1))
        (sourceUnitDirection (graphPlaneAngle p.1.2-Real.arctan p.1.1+axis))) :=
    hF.comp (show Measurable (fun p : (ℝ × Plane) × α =>
      ((R*(‖p.1.2‖*Real.sqrt (1+p.1.1^2)/2),
        (sourceUnitDirection (graphPlaneAngle p.1.2+Real.arctan p.1.1),
         sourceUnitDirection (graphPlaneAngle p.1.2-Real.arctan p.1.1+axis))), p.2)) from by fun_prop)
  unfold graphTransport
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · apply Measurable.mul
    · apply Complex.measurable_ofReal.comp
      exact hΨ.comp (show Measurable (fun p : (ℝ × Plane) × α =>
        ‖p.1.2‖*Real.sqrt (1+p.1.1^2)/2) from by fun_prop)
    · exact hg

theorem graphFourKernel_spatial_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    Integrable (fun p : (ℝ × Plane) × (Fin 4 → Plane) =>
      graphTransport (graphFourKernel b W p.2) Ψ R axis p.1) (volume.prod μ) := by
  have hB' := mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))
  apply compact_finite_spatial_integrable volume μ graphTransportBox_compact.measurableSet
    graphTransportBox_compact.measure_lt_top
    (graphTransport_family_measurable _ (graphFourKernel_measurable b W hb hW) hΨ R axis)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hC hB'))
  · intro p
    exact graphTransport_norm_le hsupp hB' hC
      (graphFourKernel_norm_le b W B hB hbound hw p.2) hc R axis p.1
  · intro p hp
    exact graphTransport_support hsupp R axis
      (fun r φ z hn => hchart φ z (graphFourKernel_weight_ne_zero b W p.2 r _ _ hn)) hp

theorem graphFourKernel_spatial_chart
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hbcont : ∀ i x, Continuous (b i x)) (hW : Continuous W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) (axis : ℝ)
    (hchart : ∀ φ z, W (sourceUnitDirection (φ+Real.arctan z),
      sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    R⁻¹ • (∫ x, ∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
      ∂sourceArcLength ∂sourceArcLength ∂volume ∂μ) =
      ∫ p : ℝ × Plane, ∫ x, graphTransport (graphFourKernel b W x) Ψ R axis p ∂μ := by
  rw [← integral_smul]
  simp_rw [graphFourKernel_chart_product b W hbcont hW B hB hbound hw hΨ hsupp hC hc hR axis hchart]
  exact integral_integral_swap
    (graphFourKernel_spatial_integrable μ b W hb hW.measurable B hB hbound hw hΨ.measurable
      hsupp hC hc R axis hchart).swap

end PlanarFalconer

end OAI

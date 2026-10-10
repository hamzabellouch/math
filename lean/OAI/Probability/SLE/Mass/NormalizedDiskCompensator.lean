import OAI.Probability.SLE.Geometry.CanonicalNormalizedPotential
import OAI.Probability.SLE.Mass.CanonicalMassCompensator

namespace OAI

/-! Recovery of the actual canonical disk mass on the exact target
Brownian-time dyadic grid. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

def normalizedDiskScalar (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (t : ℝ≥0) (ω : Ω) : ℝ := C.diskScalar θ hθ (t/κ.toNNReal) ω

lemma normalizedDiskScalar_measurable (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (t : ℝ≥0) : Measurable (C.normalizedDiskScalar θ hθ t) :=
  (compactWeightedMass_measurable _ _
    (Target.diskSourceHalfPlane_compact hθ).measurableSet).comp
      C.progressive.adapted.measurable

lemma normalizedDiskScalar_integrable (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
    (t : ℝ≥0) : Integrable (C.normalizedDiskScalar θ hθ t) P := by
  exact (compactWeightedMass_kernel_integrable P κ (C.process (t/κ.toNNReal))
    C.progressive.adapted.measurable
    (by simpa only [Measure.restrict_univ] using
      C.uniqueness_process_mean_le (t/κ.toNNReal) univ)
    _ _ (Target.diskSourceHalfPlane_compact hθ)).1

lemma normalizedDiskScalar_stronglyAdapted (hκ : 0<κ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    StronglyAdapted (Target.normalizedFiltration κ B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0)
      (C.normalizedDiskScalar θ hθ) := by
  intro t
  erw [Target.normalizedFiltration_at κ hκ]
  exact ((compactWeightedMass_measurable _ _
    (Target.diskSourceHalfPlane_compact hθ).measurableSet).comp
      (C.progressive.adapted (t/κ.toNNReal))).stronglyMeasurable

theorem normalizedDiskScalar_paths (hκ : 0<κ)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    ∀ᵐ ω ∂P, Monotone (fun t => C.normalizedDiskScalar θ hθ t ω) ∧
      C.normalizedDiskScalar θ hθ 0 ω=0 ∧
      Continuous (fun t => C.normalizedDiskScalar θ hθ t ω) ∧
      Tendsto (fun t => C.normalizedDiskScalar θ hθ t ω) atTop
        (𝓝 (C.diskTerminalScalar θ hθ ω)) ∧
      ∀ t, C.normalizedDiskScalar θ hθ t ω ≤ C.diskTerminalScalar θ hθ ω := by
  filter_upwards [C.compactWeightedMass_paths (Target.diskMassWeight κ θ hθ)
    (Target.diskSourceHalfPlane θ) (Target.diskSourceHalfPlane_compact hθ)] with ω hω
  refine ⟨?_,?_,hω.2.2.1.comp (continuous_id.div_const _),?_,fun t => hω.2.2.2.2 _⟩
  · intro s t hst
    exact hω.1 (div_le_div_of_nonneg_right hst zero_le)
  · simpa only [normalizedDiskScalar,diskScalar,zero_div] using hω.2.1
  · exact hω.2.2.2.1.comp
      ((tendsto_div_const_atTop_of_pos (Real.toNNReal_pos.mpr hκ)).mpr tendsto_id)

theorem normalized_disk_compensator_recovery [IsProbabilityMeasure P]
    (hκ : 0<κ) (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (T : Ω → ℝ≥0∞) (hT : Measurable T) :
    TendstoInMeasure P
      (fun n ω => meshMassCompensator P
        (compensatorMeshFiltration (Target.normalizedFiltration κ B
          (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0))
        (C.normalizedDiskScalar θ hθ) n (compensatorStopIndex n (T ω)) ω) atTop
      (fun ω => massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
        (C.diskTerminalScalar θ hθ ω) (T ω)) := by
  apply meshMassCompensator_stopped_tendstoInMeasure P _ _ _ _ _
    (C.compactWeightedMass_terminal_memLp _ _ (Target.diskSourceHalfPlane_compact hθ))
    (C.normalizedDiskScalar_paths hκ θ hθ) T hT
  · intro t
    exact C.normalizedDiskScalar_measurable θ hθ t
  · intro n i
    change StronglyMeasurable[Target.normalizedFiltration κ B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)))
      hc h0 (compensatorMeshTime n i)] _
    exact C.normalizedDiskScalar_stronglyAdapted hκ hc h0 θ hθ _

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

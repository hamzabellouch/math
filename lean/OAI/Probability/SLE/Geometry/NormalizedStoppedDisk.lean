import OAI.Probability.SLE.Mass.NormalizedDiskCompensator

namespace OAI

/-! Measurable finite-or-terminal evaluation of the canonical disk mass
on the normalized Brownian time scale. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma normalizedStoppedDisk_measurable
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (T : Ω → ℝ≥0∞) (hT : Measurable T) :
    Measurable (fun ω => massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
      (C.diskTerminalScalar θ hθ ω) (T ω)) := by
  have hw := compactWeightedMass_measurable (Target.diskMassWeight κ θ hθ)
    (Target.diskSourceHalfPlane θ) (Target.diskSourceHalfPlane_compact hθ).measurableSet
  have hm := _root_.OAI.MeasureTheory.IsProgressive.random_time_measurable C.progressive
    (fun ω => (T ω).toNNReal/κ.toNNReal) (hT.ennreal_toNNReal.div_const _)
  exact (hw.comp C.rational.terminal_measurable).ite
    (measurableSet_eq_fun hT measurable_const) (hw.comp hm)

lemma normalizedStoppedDisk_nonneg
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (T : ℝ≥0∞) (ω : Ω) :
    0 ≤ massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
      (C.diskTerminalScalar θ hθ ω) T := by
  unfold massAtExtendedTime
  split_ifs <;> exact compactWeightedMass_nonneg _ _ _

lemma normalizedStoppedDisk_le_terminal
    (hκ : 0<κ) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (T : Ω → ℝ≥0∞) :
    ∀ᵐ ω ∂P, massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
      (C.diskTerminalScalar θ hθ ω) (T ω) ≤ C.diskTerminalScalar θ hθ ω := by
  filter_upwards [C.normalizedDiskScalar_paths hκ θ hθ] with ω hp
  unfold massAtExtendedTime
  split_ifs
  · exact le_rfl
  · exact hp.2.2.2.2 _

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI

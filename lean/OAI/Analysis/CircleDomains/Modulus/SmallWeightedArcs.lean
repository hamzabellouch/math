import OAI.Analysis.CircleDomains.Modulus.AffineRectifiableLength
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! Absolute continuity of finite weighted arclength gives arbitrarily
cheap short parameter arcs through every point, including density singularities. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_small_time_interval (μ : Measure PathTime) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (r : PathTime) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : PathTime, dist s r < δ → dist t r < δ →
      μ (Icc (min s t) (max s t)) < ε := by
  obtain ⟨V, hrV, hV, hμV⟩ := Set.exists_isOpen_lt_of_lt (μ := μ) {r} ε (by simpa using hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hrV (mem_singleton r)))
  refine ⟨δ, hδ, fun s t hs ht => (measure_mono ?_).trans_lt hμV⟩
  intro u hu
  apply hball
  change |(u : ℝ) - r| < δ
  change |(s : ℝ) - r| < δ at hs
  change |(t : ℝ) - r| < δ at ht
  rw [abs_lt] at hs ht ⊢
  have hlo : (r : ℝ) - δ < min (s : ℝ) t := lt_min (by linarith [hs.1]) (by linarith [ht.1])
  have hhi : max (s : ℝ) t < (r : ℝ) + δ := max_lt (by linarith [hs.2]) (by linarith [ht.2])
  change min (s : ℝ) t ≤ (u : ℝ) ∧ (u : ℝ) ≤ max (s : ℝ) t at hu
  constructor <;> linarith

variable {X : Type*} [MetricSpace X]

theorem exists_small_weighted_arcs (γ : RectifiablePath X) (g : X → ℝ≥0∞)
    (hfinite : (∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ) < ∞)
    (r : PathTime) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : PathTime, dist s r < δ → dist t r < δ →
      (∫⁻ v in Icc (min s t) (max s t), g (γ.val v) ∂pathLengthMeasure γ) < ε := by
  let μ := (pathLengthMeasure γ).withDensity (fun t => g (γ.val t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity hfinite.ne
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_time_interval μ r hε
  refine ⟨δ, hδ, fun s t hs ht => ?_⟩
  simpa only [μ, withDensity_apply _ measurableSet_Icc] using hsmall s t hs ht

end CircleDomainRigidity

end

end OAI

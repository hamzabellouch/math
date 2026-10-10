import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

variable {X E 𝕜 : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [NormedAddCommGroup E] [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] [SecondCountableTopologyEither X E]
  {μ : Measure X} [IsFiniteMeasure μ]

omit [BorelSpace X] [CompactSpace X] [SecondCountableTopologyEither X E]
  [IsFiniteMeasure μ] in

theorem continuous_norm_le_of_ae [μ.IsOpenPosMeasure] (f : C(X, E)) {C : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ∀ x, ‖f x‖ ≤ C := by
  have hclosed : IsClosed {x | ‖f x‖ ≤ C} :=
    isClosed_le f.continuous.norm continuous_const
  intro x
  have hx := (μ.dense_of_ae h) x
  rwa [hclosed.closure_eq] at hx

theorem norm_continuous_toLp_top [μ.IsOpenPosMeasure] (f : C(X, E)) :
    ‖ContinuousMap.toLp (E := E) ∞ μ 𝕜 f‖ = ‖f‖ := by
  let u : Lp E ∞ μ := ContinuousMap.toLp ∞ μ 𝕜 f
  have hrep : u =ᵐ[μ] f := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := 𝕜) μ f
  have hnorm : ‖u‖ = lpNorm f ∞ μ := by
    rw [Lp.norm_def, eLpNorm_congr_ae hrep, toReal_eLpNorm]
  apply le_antisymm
  · have hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f‖ := by
      filter_upwards [hrep] with x hx
      rw [hx]
      exact f.norm_coe_le_norm x
    have hu := Lp.norm_le_of_ae_bound (norm_nonneg f) hb
    simpa using hu
  · apply (ContinuousMap.norm_le f (norm_nonneg _)).mpr
    apply continuous_norm_le_of_ae (μ := μ) f
    rw [hnorm]
    exact ae_le_lpNorm_exponent_top (ContinuousMap.memLp (p := ∞) μ 𝕜 f)

end Invariant233

end OAI

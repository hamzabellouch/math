import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LeftRightNhds

namespace OAI

/-!
# A nonzero self-similar amplitude prevents continuous continuation

A positive self-similar amplitude excludes continuous continuation through
the singular time.
-/

open Filter Topology

namespace DefocusingNLS

/-- A positive power times a function with a finite left limit tends to zero. -/
theorem vanishing_rescaled_norm_of_left_limit {E : Type*} [NormedAddCommGroup E]
    (u : ℝ → E) (T a : ℝ) (ha : 0 < a) (v : E)
    (hu : Tendsto u (𝓝[<] T) (𝓝 v)) :
    Tendsto (fun t => (T - t) ^ a * ‖u t‖) (𝓝[<] T) (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => T) (𝓝[<] T) (𝓝 T) := tendsto_const_nhds
    simpa using (hconst.sub (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T)))
  have hpow : Tendsto (fun t : ℝ => (T - t) ^ a) (𝓝[<] T) (𝓝 0) := by
    simpa [Function.comp_def, Real.zero_rpow ha.ne'] using
      (Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp hbase
  simpa using hpow.mul hu.norm

/-- In particular, the positive rescaled limit in the paper excludes a finite left limit. -/
theorem no_left_limit_of_positive_rescaled_norm {E : Type*} [NormedAddCommGroup E]
    (u : ℝ → E) (T a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hblowup : Tendsto (fun t => (T - t) ^ a * ‖u t‖) (𝓝[<] T) (𝓝 c)) :
    ¬ ∃ v, Tendsto u (𝓝[<] T) (𝓝 v) := by
  rintro ⟨v, hv⟩
  have hzero := vanishing_rescaled_norm_of_left_limit u T a ha v hv
  have heq : c = 0 := tendsto_nhds_unique hblowup hzero
  exact hc.ne' heq

/-- Continuous observations of a continuously extendible trajectory have a finite left limit.
Hence a positive self-similar pointwise amplitude rules out such an extension. -/
theorem no_continuous_extension_of_positive_rescaled_norm
    {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    (u : ℝ → E) (observe : E → F) (T a c : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hobs : Continuous observe)
    (hblowup : Tendsto (fun t => (T - t) ^ a * ‖observe (u t)‖)
      (𝓝[<] T) (𝓝 c)) :
    ¬ ContinuousWithinAt u (Set.Iio T) T := by
  intro hu
  apply no_left_limit_of_positive_rescaled_norm (fun t => observe (u t)) T a c ha hc
    hblowup
  exact ⟨observe (u T), hobs.continuousAt.tendsto.comp hu⟩

end DefocusingNLS

end OAI

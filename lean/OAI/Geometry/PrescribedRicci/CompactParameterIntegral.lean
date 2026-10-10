import Mathlib

namespace OAI

/-! Compact Parameter Integral. -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace KahlerCalculus
variable {E : Type*} [TopologicalSpace E] [T2Space E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

lemma hasDerivAt_integral_compact {F F' : ℝ → E → ℝ} {K : Set E}
    (hK : IsCompact K) (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hs : ∀ t, Function.support (F t) ⊆ K)
    (hs' : ∀ t, Function.support (F' t) ⊆ K)
    (hd : ∀ t z, HasDerivAt (fun s => F s z) (F' t z) t) (t : ℝ) :
    HasDerivAt (fun s => ∫ z, F s z ∂μ) (∫ z, F' t z ∂μ) t := by
  have hfc (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hfc' (s : ℝ) : Continuous (F' s) := hF'.comp (continuous_const.prodMk continuous_id)
  have hfi (s : ℝ) : Integrable (F s) μ := (hfc s).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact hK (hs s))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t - 1) (b := t + 1)).prod hK
    |>.exists_bound_of_continuousOn hF'.continuousOn
  let B : E → ℝ := K.indicator (fun _ => max C 0)
  have hB : Integrable B μ := by
    apply (integrable_indicator_iff hK.measurableSet).mpr
    exact integrableOn_const hK.measure_lt_top.ne
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (Filter.Eventually.of_forall (fun s => (hfc s).aestronglyMeasurable)) (hfi t)
    (hfc' t).aestronglyMeasurable ?_ hB ?_).2
  · filter_upwards [] with z s hst
    by_cases hz : z ∈ K
    · exact (hC (s, z) ⟨⟨hst.1.le, hst.2.le⟩, hz⟩).trans
        (by simpa only [B, Set.indicator_of_mem hz] using le_max_left C 0)
    · have he : F' s z = 0 := Function.notMem_support.mp (fun hn => hz (hs' s hn))
      simp only [he, norm_zero, B, Set.indicator_of_notMem hz, le_refl]
  · exact Filter.Eventually.of_forall (fun z s _ => hd s z)

end KahlerCalculus

end

end OAI

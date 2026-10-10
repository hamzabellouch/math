import OAI.Geometry.RCD.Metric.RescaledEvolution

namespace OAI

/-! # Passing an integrated evolution estimate to the initial time -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem continuous_gronwall_initial (k e : ℝ) :
    Continuous (fun z : ℝ × ℝ => gronwallBound z.1 k e z.2) := by
  by_cases hk : k=0
  · simp only [hk,gronwallBound_K0]
    fun_prop
  · simp only [gronwallBound_of_K_ne_0 hk]
    fun_prop

theorem evolution_initial_limit {D : ℝ → ℝ} {k e b : ℝ} (hb : 0 < b)
    (hD : ContinuousOn D (Icc 0 b))
    (hbound : ∀ a, 0 < a → a ≤ b → D b ≤ gronwallBound (D a) k e (b-a)) :
    D b ≤ gronwallBound (D 0) k e b := by
  have hc : ContinuousWithinAt D (Ioi 0) 0 :=
    ((hD 0 ⟨le_rfl,hb.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hb)).mono Ioi_subset_Ici_self
  have hl : Tendsto (fun a => gronwallBound (D a) k e (b-a)) (𝓝[>] 0)
      (𝓝 (gronwallBound (D 0) k e b)) := by
    have hp := hc.tendsto.prodMk_nhds
      ((continuous_const.sub continuous_id).continuousAt.continuousWithinAt.tendsto :
        Tendsto (fun a : ℝ => b-a) (𝓝[>] 0) (𝓝 (b-0)))
    simpa only [Function.comp_def,Pi.sub_apply,id_eq,sub_zero] using
      (continuous_gronwall_initial k e).continuousAt.tendsto.comp hp
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hb)] with a ha ha'
  exact hbound a ha (le_of_lt ha')

end RegularPointCoordinates

end OAI

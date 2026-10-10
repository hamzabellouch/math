import OAI.Geometry.RCD.Metric.DimensionalRateContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Passing a bounded cost/entropy approximation through the dimensional rate -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem integral_dimensionalEntropyRate_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K N a b e M : ℝ} (hK : K ≤ 0) (hN : 0 < N) (hab : a ≤ b)
    {W : ι → ℝ → ℝ} {F : ι → ℝ} {D P : ℝ → ℝ}
    (hW : ∀ᶠ i in l, ContinuousOn (W i) (Icc a b)) (hP : ContinuousOn P (Icc a b))
    (hwl : ∀ t ∈ Icc a b, Tendsto (fun i => W i t) l (𝓝 (D t)))
    (hfl : Tendsto F l (𝓝 e))
    (hbound : ∀ᶠ i in l, ∀ t ∈ Icc a b,
      |W i t| ≤ M ∧ |P t| ≤ M ∧ |F i| ≤ M) :
    Tendsto (fun i => ∫t in a..b, dimensionalEntropyRate K N (W i t,P t,F i)) l
      (𝓝 (∫t in a..b, dimensionalEntropyRate K N (D t,P t,e))) := by
  let H := dimensionalEntropyRate K N
  have hH : Continuous H := continuous_dimensionalEntropyRate hK hN
  let S : Set (ℝ × ℝ × ℝ) := Icc (-M) M ×ˢ (Icc (-M) M ×ˢ Icc (-M) M)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C,hC⟩ := hS.bddAbove_image hH.norm.continuousOn
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · filter_upwards [hW] with i hWi
    have hc : ContinuousOn (fun t => H (W i t,P t,F i)) (Icc a b) :=
      hH.comp_continuousOn (hWi.prodMk (hP.prodMk continuousOn_const))
    apply (hc.mono _).aestronglyMeasurable measurableSet_uIoc
    simpa only [uIcc_of_le hab] using (uIoc_subset_uIcc : uIoc a b ⊆ uIcc a b)
  · filter_upwards [hbound] with i hi
    exact Eventually.of_forall fun t ht => by
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
      have hh := hi t ht'
      exact hC (mem_image_of_mem (fun z => ‖H z‖) ⟨abs_le.mp hh.1,abs_le.mp hh.2.1,abs_le.mp hh.2.2⟩)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht => by
      have ht' : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
      exact (hH.tendsto _).comp ((hwl t ht').prodMk_nhds (tendsto_const_nhds.prodMk_nhds hfl))

end RegularPointCoordinates

end

end OAI

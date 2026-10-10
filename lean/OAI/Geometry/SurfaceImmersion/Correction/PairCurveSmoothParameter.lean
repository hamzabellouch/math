import OAI.Geometry.SurfaceImmersion.Geometry.PairCurveParameter

namespace OAI

/-! The chart parameter for a smooth pair curve is smooth on an actual
open neighborhood, as required by the global parameter-germ extension. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem smooth_pair_curve_parameter (c : SmoothDoubleChart f) {C : ℝ → M × M}
    {W : Set ℝ} (hW : IsOpen W) (hC : ContMDiffOn 𝓘(ℝ) (planeModel.prod planeModel) ∞ C W)
    {x : ℝ} (hx : x ∈ W) (p : surfaceDoublePairs f) (hp : p.val = C x) (hpc : p ∈ c.coord.source)
    (hpair : Function.Injective
      ((mfderiv 𝓘(ℝ) planeModel (fun t => (C t).1) x).prod
        (mfderiv 𝓘(ℝ) planeModel (fun t => (C t).2) x)))
    (hgood : ∀ᶠ t in 𝓝 x, C t ∈ surfaceDoublePairs f) :
    ∃ (U : Set ℝ) (h : ℝ → ℝ), IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      ContDiffOn ℝ ∞ h U ∧ deriv h x ≠ 0 ∧ h x = c.coord p ∧
      C =ᶠ[𝓝 x] (fun t => (c.coord.symm (h t)).val) := by
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (C t).1) W :=
    contMDiff_fst.comp_contMDiffOn hC
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (C t).2) W :=
    contMDiff_snd.comp_contMDiffOn hC
  obtain ⟨g,hg,hgn,hgv,hginv⟩ := c.pair_curve_parameter p hp hpc
    (hA.contMDiffAt (hW.mem_nhds hx)) (hB.contMDiffAt (hW.mem_nhds hx)) hpair hgood
  let U := W ∩ C ⁻¹' ((chart c.left).source ×ˢ (chart c.right).source)
  have hU : IsOpen U := hC.continuousOn.isOpen_inter_preimage hW
    ((chart c.left).open_source.prod (chart c.right).open_source)
  have hxU : x ∈ U := by
    refine ⟨hx,?_⟩
    change C x ∈ (chart c.left).source ×ˢ (chart c.right).source
    rw [← hp]
    exact ⟨(c.source_formula p hpc).1,(c.source_formula p hpc).2.1⟩
  let h : ℝ → ℝ := fun t => c.expression (chart c.left (C t).1,chart c.right (C t).2)
  have hleft := (chart_smooth c.left).comp (hA.mono (show U ⊆ W from inter_subset_left)) (fun t (ht : t ∈ U) => ht.2.1)
  have hright := (chart_smooth c.right).comp (hB.mono (show U ⊆ W from inter_subset_left)) (fun t (ht : t ∈ U) => ht.2.2)
  have hs : ContDiffOn ℝ ∞ h U := c.expression_smooth.comp_contDiffOn
    (hleft.contDiffOn.prodMk hright.contDiffOn)
  have hgtarget : ∀ᶠ t in 𝓝 x, g t ∈ c.coord.target :=
    hg.continuousAt.eventually (c.coord.open_target.mem_nhds (hgv ▸ c.coord.map_source hpc))
  have he : h =ᶠ[𝓝 x] g := by
    filter_upwards [hginv,hgtarget] with t ht ht'
    change c.expression (chart c.left (C t).1,chart c.right (C t).2) = g t
    rw [ht]
    exact (c.source_formula (c.coord.symm (g t)) (c.coord.map_target ht')).2.2.symm.trans
      (c.coord.right_inv ht')
  refine ⟨U,h,hU,hxU,inter_subset_left,hs,?_,he.eq_of_nhds.trans hgv,?_⟩
  · rw [he.deriv_eq]
    exact hgn
  · filter_upwards [hginv,he] with t ht ht'
    rw [ht']
    exact ht

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Atlas.CompactTimeChart
import OAI.Geometry.SurfaceImmersion.Geometry.TimeBlendDomain
import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTimeOverlap

namespace OAI

/-! Adjacent charts straightening the same regular arc can be joined,
retaining the longitudinal coordinate and both exterior axis germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] [Nonempty M]

theorem join_time_charts {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    {γ : ℝ → M} {a b e : ℝ} (hab : a < b) (hbe : b < e)
    (hγ : ∀ t ∈ Icc a e, ContinuousAt γ t)
    {W : Set ℝ} (hW : W ∈ 𝓝 b) (hIW : Icc a e ⊆ W)
    (c d : SurfaceTimeChart F)
    (hc : ∀ t ∈ Icc a b, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ c.coord.source ∧ c.coord (γ s) = ![0,s])
    (hd : ∀ t ∈ Icc b e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ d.coord.source ∧ d.coord (γ s) = ![0,s]) :
    ∃ k : SurfaceTimeChart F, ∀ t ∈ Icc a e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ k.coord.source ∧ k.coord (γ s) = ![0,s] := by
  have hcb : ∀ᶠ s in 𝓝 b, γ s ∈ c.coord.source ∧ c.coord (γ s) = ![0,s] := by
    simpa only [nhdsWithin_eq_nhds.mpr hW] using hc b ⟨hab.le,le_rfl⟩
  have hdb : ∀ᶠ s in 𝓝 b, γ s ∈ d.coord.source ∧ d.coord (γ s) = ![0,s] := by
    simpa only [nhdsWithin_eq_nhds.mpr hW] using hd b ⟨le_rfl,hbe.le⟩
  obtain ⟨d',hsource,haxis,hpos⟩ := c.positive_transition d (γ b)
    (Filter.Eventually.self_of_nhds hcb).1 (Filter.Eventually.self_of_nhds hdb).1
  have hd' : ∀ t ∈ Icc b e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ d'.coord.source ∧ d'.coord (γ s) = ![0,s] := by
    intro t ht
    filter_upwards [hd t ht] with s hs
    exact ⟨hsource.symm ▸ hs.1,haxis _ _ hs.2⟩
  have hdb' : ∀ᶠ s in 𝓝 b, γ s ∈ d'.coord.source ∧ d'.coord (γ s) = ![0,s] := by
    simpa only [nhdsWithin_eq_nhds.mpr hW] using hd' b ⟨le_rfl,hbe.le⟩
  obtain ⟨V,hV,hbV,hVsub,hVpos⟩ := c.positive_overlap d' (γ b)
    (Filter.Eventually.self_of_nhds hcb).1 (Filter.Eventually.self_of_nhds hdb').1 hpos
  have hcommon : ∀ᶠ s in 𝓝 b, γ s ∈ V ∧
      (γ s ∈ c.coord.source ∧ c.coord (γ s) = ![0,s]) ∧
      (γ s ∈ d'.coord.source ∧ d'.coord (γ s) = ![0,s]) := by
    filter_upwards [(hγ b ⟨hab.le,hbe.le⟩).eventually (hV.mem_nhds hbV),hcb,hdb'] with s hs hcs hds
    exact ⟨hs,hcs,hds⟩
  obtain ⟨O,hOsub,hO,hbO⟩ := eventually_nhds_iff.mp hcommon
  obtain ⟨l,r,hal,hlb,hbr,hre,hlrsub⟩ :=
    straddling_compact_interval hab hbe (hO.mem_nhds hbO)
  have hlr : l < r := hlb.trans hbr
  let H := surfaceTimeBlend c d' (timeCutoff l r)
  let U := timeBlendDomain c d' l r
  have hU : IsOpen U := timeBlendDomain_open c d' l r hF.continuous
  have hHgerm : ∀ t ∈ Icc a e, ∀ᶠ s in 𝓝[W] t,
      γ s ∈ U ∧ H (γ s) = ![0,s] := by
    intro t ht
    by_cases htl : t < l
    · have hct := hc t ⟨ht.1,htl.le.trans hlb.le⟩
      filter_upwards [hct,nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htl)] with s hs hsl
      refine ⟨Or.inl (Or.inl ⟨hs.1,?_⟩),?_⟩
      · change F (γ s) < l
        rw [← c.time _ hs.1,hs.2]
        exact hsl
      · change surfaceTimeBlend c d' (timeCutoff l r) (γ s) = _
        rw [surfaceTimeBlend_zero c d' (timeCutoff_zero hlr ?_)]
        · exact hs.2
        · rw [← c.time _ hs.1,hs.2]; exact hsl.le
    · by_cases hrt : r < t
      · have hdt := hd' t ⟨hbr.le.trans hrt.le,ht.2⟩
        filter_upwards [hdt,nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hrt)] with s hs hrs
        refine ⟨Or.inr ⟨hs.1,?_⟩,?_⟩
        · change r < F (γ s)
          rw [← d'.time _ hs.1,hs.2]; exact hrs
        · change surfaceTimeBlend c d' (timeCutoff l r) (γ s) = _
          rw [surfaceTimeBlend_one c d' (timeCutoff_one hlr ?_)]
          · exact hs.2
          · rw [← d'.time _ hs.1,hs.2]; exact hrs.le
      · have htO := hlrsub ⟨le_of_not_gt htl,le_of_not_gt hrt⟩
        filter_upwards [nhdsWithin_le_nhds (hO.mem_nhds htO)] with s hs
        have hsc := hOsub s hs
        exact ⟨Or.inl (Or.inr ⟨hsc.2.1.1,hsc.2.2.1⟩),
          surfaceTimeBlend_axis c d' hsc.2.1.2 hsc.2.2.2⟩
  let K := γ '' Icc a e
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (fun t ht => (hγ t ht).continuousWithinAt)
  have hKU : K ⊆ U := by
    rintro x ⟨t,ht,rfl⟩
    exact (mem_of_mem_nhdsWithin (hIW ht) (hHgerm t ht)).1
  have hHi : K.InjOn H := by
    rintro x ⟨t,ht,rfl⟩ y ⟨s,hs,rfl⟩ heq
    have hta := (mem_of_mem_nhdsWithin (hIW ht) (hHgerm t ht)).2
    have hsa := (mem_of_mem_nhdsWithin (hIW hs) (hHgerm s hs)).2
    have hts : t = s := by
      have hh := congrFun (hta.symm.trans (heq.trans hsa)) (1:Fin 2)
      exact hh
    rw [hts]
  have hHr : ∀ x ∈ K, Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) H x) := by
    rintro x ⟨t,ht,rfl⟩
    by_cases htl : t < l
    · have hct := mem_of_mem_nhdsWithin (hIW ht) (hc t ⟨ht.1,htl.le.trans hlb.le⟩)
      have hFt : F (γ t) = t := by rw [← c.time _ hct.1,hct.2]; rfl
      have heq := surfaceTimeBlend_left_germ c d' hF.continuous hlr (hFt ▸ htl)
      change Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base)
        (surfaceTimeBlend c d' (timeCutoff l r)) (γ t))
      rw [heq.mfderiv_eq]
      exact c.regular hct.1
    · by_cases hrt : r < t
      · have hdt := mem_of_mem_nhdsWithin (hIW ht) (hd' t ⟨hbr.le.trans hrt.le,ht.2⟩)
        have hFt : F (γ t) = t := by rw [← d'.time _ hdt.1,hdt.2]; rfl
        have heq := surfaceTimeBlend_right_germ c d' hF.continuous hlr (hFt ▸ hrt)
        change Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base)
          (surfaceTimeBlend c d' (timeCutoff l r)) (γ t))
        rw [heq.mfderiv_eq]
        exact d'.regular hdt.1
      · have htcommon := hOsub t (hlrsub ⟨le_of_not_gt htl,le_of_not_gt hrt⟩)
        exact surfaceTimeBlend_regular c d' (timeCutoff_smooth l r) hF (γ t)
          htcommon.2.1.1 htcommon.2.2.1 (htcommon.2.2.2.trans htcommon.2.1.2.symm)
          (hVpos _ htcommon.1) (timeCutoff_mem l r _)
  obtain ⟨k,hKk,hkf⟩ := compact_time_chart hK hU hKU
    (timeBlendDomain_smooth c d' hlr hF) (fun x hx => timeBlendDomain_time c d' hlr hx) hHi hHr
  refine ⟨k,?_⟩
  intro t ht
  have htk : γ t ∈ k.coord.source := hKk ⟨t,ht,rfl⟩
  filter_upwards [((hγ t ht).eventually (k.coord.open_source.mem_nhds htk)).filter_mono nhdsWithin_le_nhds,hHgerm t ht] with s hs hsg
  exact ⟨hs,(hkf hs).trans hsg.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

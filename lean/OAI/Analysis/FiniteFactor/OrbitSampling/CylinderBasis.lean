import OAI.Analysis.FiniteFactor.OrbitSampling.CylinderSystem

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem rational_Icc_nhds {x : ℝ} {u : Set ℝ} (hu : u ∈ 𝓝 x) :
    ∃ a b : ℚ, Set.Icc (a : ℝ) b ∈ 𝓝 x ∧ Set.Icc (a : ℝ) b ⊆ u := by
  obtain ⟨l,r,hlr,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hu
  obtain ⟨a,hla,hax⟩ := exists_rat_btwn hlr.1
  obtain ⟨b,hxb,hbr⟩ := exists_rat_btwn hlr.2
  exact ⟨a,b,Icc_mem_nhds hax hxb,fun y hy => hsub ⟨hla.trans_le hy.1,hy.2.trans_lt hbr⟩⟩

/-- The finite rational cylinders contain arbitrarily small neighborhoods
in the full real product, including points outside the unit cube. -/
theorem sourceSamplingCylinder_basis (u : Set SourceSamplingPair) (hu : IsOpen u)
    (p : SourceSamplingPair) (hp : p ∈ u) :
    ∃ s ∈ Set.range sourceSamplingCylinder, s ∈ 𝓝 p ∧ s ⊆ u := by
  obtain ⟨ux,hux,uy,huy,hxy⟩ := mem_nhds_prod_iff.mp (hu.mem_nhds hp)
  rw [nhds_pi,Filter.mem_pi'] at hux huy
  obtain ⟨Kx,tx,htx,hsubx⟩ := hux
  obtain ⟨Ky,ty,hty,hsuby⟩ := huy
  choose ax bx hnx hsx using fun i => rational_Icc_nhds (htx i)
  choose ay by' hny hsy using fun i => rational_Icc_nhds (hty i)
  let T : SourceSamplingRationalTest := ⟨Kx ∪ Ky,fun i => ((ax i,bx i),(ay i,by' i))⟩
  have hTx (i : SourceCoordinate) (hi : i ∈ T.1) :
      sourceSamplingRationalX T i = Set.Icc (ax i : ℝ) (bx i) := by
    simp [sourceSamplingRationalX,sourceSamplingRationalEndpoints,hi,T]
  have hTy (i : SourceCoordinate) (hi : i ∈ T.1) :
      sourceSamplingRationalY T i = Set.Icc (ay i : ℝ) (by' i) := by
    simp [sourceSamplingRationalY,sourceSamplingRationalEndpoints,hi,T]
  refine ⟨sourceSamplingCylinder T,⟨T,rfl⟩,?_,?_⟩
  · have he : sourceSamplingCylinder T = ⋂ i ∈ T.1,
        {q : SourceSamplingPair | q.1 i ∈ sourceSamplingRationalX T i ∧
          q.2 i ∈ sourceSamplingRationalY T i} := by ext q; simp [sourceSamplingCylinder]
    rw [he]
    apply (Filter.biInter_mem (Set.toFinite (T.1 : Set SourceCoordinate))).mpr
    intro i hi
    have hx := ((continuous_apply i).comp continuous_fst).continuousAt (hnx i)
    have hy := ((continuous_apply i).comp continuous_snd).continuousAt (hny i)
    change {q : SourceSamplingPair | q.1 i ∈ Set.Icc (ax i : ℝ) (bx i)} ∈ 𝓝 p at hx
    change {q : SourceSamplingPair | q.2 i ∈ Set.Icc (ay i : ℝ) (by' i)} ∈ 𝓝 p at hy
    filter_upwards [hx,hy] with q hq1 hq2
    exact ⟨by simpa only [hTx i hi] using hq1,by simpa only [hTy i hi] using hq2⟩
  · intro q hq
    apply hxy
    constructor
    · apply hsubx
      intro i hi
      have hmem : i ∈ T.1 := Finset.mem_union_left _ hi
      exact hsx i (by simpa only [hTx i hmem] using (hq i hmem).1)
    · apply hsuby
      intro i hi
      have hmem : i ∈ T.1 := Finset.mem_union_right _ hi
      exact hsy i (by simpa only [hTy i hmem] using (hq i hmem).2)

end
end FiniteFactor

end OAI

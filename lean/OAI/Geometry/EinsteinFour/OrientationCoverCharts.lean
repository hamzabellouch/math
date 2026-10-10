import OAI.Geometry.EinsteinFour.OrientationCoverTopology

namespace OAI

/-! Smooth local coordinates on the actual orientation cover. The projection
identifies each sheet with a base chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def orientationCoverLocal (x : OrientationCover M) : OpenPartialHomeomorph (OrientationCover M) M :=
  (orientationCover_isCoveringMap.isLocalHomeomorph.localInverseAt x).symm

@[simp] theorem orientationCoverLocal_apply (x y : OrientationCover M) :
    orientationCoverLocal x y = y.proj := by
  exact congrFun (orientationCover_isCoveringMap.isLocalHomeomorph.localInverseAt_symm x) y

theorem orientationCoverLocal_mem (x : OrientationCover M) :
    x ∈ (orientationCoverLocal x).source :=
  orientationCover_isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target

def orientationCoverChart (x : OrientationCover M) :
    OpenPartialHomeomorph (OrientationCover M) FourSpace :=
  (orientationCoverLocal x).trans (chartAt FourSpace x.proj)

@[simp] theorem orientationCoverChart_apply (x y : OrientationCover M) :
    orientationCoverChart x y = chartAt FourSpace x.proj y.proj := by
  change chartAt FourSpace x.proj (orientationCoverLocal x y) = _
  rw [orientationCoverLocal_apply]

theorem orientationCoverChart_mem (x : OrientationCover M) :
    x ∈ (orientationCoverChart x).source :=
  ⟨orientationCoverLocal_mem x, by change orientationCoverLocal x x ∈ (chartAt FourSpace x.proj).source; rw [orientationCoverLocal_apply]; exact mem_chart_source FourSpace x.proj⟩

theorem orientationCoverChart_inverse_proj (x : OrientationCover M) {z : FourSpace}
    (hz : z ∈ (orientationCoverChart x).target) :
    ((orientationCoverChart x).symm z).proj = (chartAt FourSpace x.proj).symm z := by
  change ((orientationCoverLocal x).symm ((chartAt FourSpace x.proj).symm z)).proj = _
  have h := (orientationCoverLocal x).right_inv hz.2
  simpa only [orientationCoverLocal_apply] using h

instance orientationCover_chartedSpace : ChartedSpace FourSpace (OrientationCover M) where
  atlas := range (orientationCoverChart (M := M))
  chartAt := orientationCoverChart
  mem_chart_source := orientationCoverChart_mem
  chart_mem_atlas x := mem_range_self x

/-- Each change of sheets uses precisely the base chart transition. -/
theorem orientationCover_transition_eq (x y : OrientationCover M) {z : FourSpace}
    (hz : z ∈ ((orientationCoverChart x).symm.trans (orientationCoverChart y)).source) :
    ((orientationCoverChart x).symm.trans (orientationCoverChart y)) z =
      chartAt FourSpace y.proj ((chartAt FourSpace x.proj).symm z) := by
  change orientationCoverChart y ((orientationCoverChart x).symm z) = _
  rw [orientationCoverChart_apply, orientationCoverChart_inverse_proj x hz.1]

theorem orientationCover_transition_source (x y : OrientationCover M) :
    ((orientationCoverChart x).symm.trans (orientationCoverChart y)).source ⊆
      ((chartAt FourSpace x.proj).symm.trans (chartAt FourSpace y.proj)).source := by
  intro z hz
  refine ⟨hz.1.1, ?_⟩
  have h := hz.2.2
  change orientationCoverLocal y ((orientationCoverChart x).symm z) ∈
    (chartAt FourSpace y.proj).source at h
  rwa [orientationCoverLocal_apply, orientationCoverChart_inverse_proj x hz.1] at h

instance orientationCover_isManifold : IsManifold I4 ∞ (OrientationCover M) := by
  apply isManifold_of_contDiffOn I4 ∞
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simp only [I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, preimage_id, range_id, inter_univ]
  change ContDiffOn ℝ ∞
    (fun z => orientationCoverChart y ((orientationCoverChart x).symm z))
    ((orientationCoverChart x).symm.trans (orientationCoverChart y)).source
  have hcompat := (contDiffGroupoid ∞ I4).compatible
    (chart_mem_atlas FourSpace x.proj) (chart_mem_atlas FourSpace y.proj)
  obtain ⟨hbase, _⟩ := hcompat
  change ContDiffOn ℝ ∞
    (I4 ∘ ((chartAt FourSpace x.proj).symm.trans (chartAt FourSpace y.proj)) ∘ I4.symm)
    (I4.symm ⁻¹' ((chartAt FourSpace x.proj).symm.trans (chartAt FourSpace y.proj)).source ∩ range I4) at hbase
  simp only [I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_def, id_eq, preimage_id, range_id, inter_univ] at hbase
  apply (hbase.mono (orientationCover_transition_source x y)).congr
  intro z hz
  exact orientationCover_transition_eq x y hz

end
end PositiveEinsteinFour.Geometry

end OAI

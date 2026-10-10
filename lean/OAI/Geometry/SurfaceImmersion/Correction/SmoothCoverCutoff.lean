import OAI.Geometry.Immersion.ClosedSurface.MetricModel
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI

/-! A smooth two-set cutoff with closed supports inside the prescribed
open cover of the compact surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem smooth_cover_cutoff {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    ∃ χ : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ U ∧ tsupport (fun p => 1-χ p) ⊆ V ∧
      ∀ p, χ p ∈ Icc (0 : ℝ) 1 := by
  have hd : Disjoint Uᶜ Vᶜ := by
    apply disjoint_left.mpr
    intro p hpU hpV
    have hp : p ∈ U ∪ V := by rw [hcover]; trivial
    exact hp.elim hpU hpV
  obtain ⟨χ,hzero,hone,hrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    planeModel hU.isClosed_compl hV.isClosed_compl hd (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hrange⟩
  · intro p hp
    by_contra hnot
    have hz : (χ : M → ℝ) =ᶠ[𝓝 p] 0 := hzero.filter_mono (nhds_le_nhdsSet hnot)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hp
  · intro p hp
    by_contra hnot
    have ho := hone.filter_mono (nhds_le_nhdsSet hnot)
    have hz : (fun q => 1-χ q) =ᶠ[𝓝 p] (0 : M → ℝ) := by
      filter_upwards [ho] with q hq
      simp only [hq,sub_self,Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hp

end ClosedSurfaceR4

end

end OAI

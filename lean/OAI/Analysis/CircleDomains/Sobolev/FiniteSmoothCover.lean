import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace OAI

/-! A finite smooth partition subordinate to bounded neighborhoods of a
compact planar set, retaining compact supports and exact sum one. -/
open Set Function Metric Bornology
open scoped Topology Manifold ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma exists_finite_smooth_cover {K : Set ℂ} (hK : IsCompact K)
    (U : K → Set ℂ) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x : K, (x : ℂ) ∈ U x)
    (hb : ∀ x, IsBounded (U x)) :
    ∃ (I : Finset K) (ρ : I → ℂ → ℝ),
      (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ i) ⊆ U i.val) ∧
      (∀ z ∈ K, ∑ i, ρ i z = 1) := by
  classical
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hxU ⟨z,hz⟩⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover U hU hcover
  have hcover' : K ⊆ ⋃ i : I, U i.val := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp (hI hz)
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hzx⟩
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ,ℂ)) hK.isClosed (fun i : I => U i.val) (fun i => hU i.val) hcover'
  refine ⟨I,fun i z => p i z,?_,?_,hp,?_⟩
  · intro i
    exact contMDiff_iff_contDiff.mp (p i).contMDiff
  · intro i
    exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _,(hb i.val).subset (hp i)⟩
  · intro z hz
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hz

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.PositivePartitionSmoothing

namespace OAI

/-! Shrinking sampling sets preserve the exact continuous boundary trace
of a partition smoothing. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def boundaryPaste (U : Set EuclideanPlane) (u v : EuclideanPlane → ℝ)
    (x : EuclideanPlane) : ℝ := by
  classical
  exact if x ∈ U then v x else u x

 theorem boundaryPaste_continuous
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*}
    (ρ : OpenPlanePartition Ω ι) (W : ι → Set EuclideanPlane)
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : ContinuousOn v Ω)
    (hsmall : ∀ x ∈ Ω, ∀ j, ρ.weight j x ≠ 0 → ∀ y ∈ W j,
      dist y x ≤ infDist x (Ω : Set EuclideanPlane)ᶜ)
    (hband : ∀ x ∈ Ω, ∀ a b : ℝ,
      (∀ j, ρ.weight j x ≠ 0 → ∀ y ∈ W j, u y ∈ Icc a b) → v x ∈ Icc a b) :
    Continuous (boundaryPaste Ω u v) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ (Ω : Set EuclideanPlane)
  · apply (hv.continuousAt (Ω.isOpen.mem_nhds hp)).congr
    filter_upwards [Ω.isOpen.mem_nhds hp] with x hx
    simp only [boundaryPaste, ite_eq_left hx]
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, huc⟩ := Metric.continuousAt_iff.mp (hu.continuousAt (x := p))
      (ε / 2) (by linarith)
    refine ⟨δ / 2, by linarith, ?_⟩
    intro x hx
    simp only [boundaryPaste, ite_eq_right hp]
    by_cases hxΩ : x ∈ (Ω : Set EuclideanPlane)
    · rw [ite_eq_left hxΩ]
      have hrange : v x ∈ Icc (u p - ε / 2) (u p + ε / 2) := by
        apply hband x hxΩ
        intro j hj y hy
        have hxy := hsmall x hxΩ j hj y hy
        have hdist : dist y p < δ := by
          have hi : infDist x (Ω : Set EuclideanPlane)ᶜ ≤ dist x p := infDist_le_dist_of_mem hp
          calc
            dist y p ≤ dist y x + dist x p := dist_triangle _ _ _
            _ ≤ 2 * dist x p := by linarith
            _ < δ := by linarith
        have he : |u y - u p| < ε / 2 := by
          simpa only [Real.dist_eq] using huc hdist
        have hh := abs_lt.mp he
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [Real.dist_eq]
      have ha : |v x - u p| ≤ ε / 2 := abs_le.mpr
        ⟨by linarith [hrange.1], by linarith [hrange.2]⟩
      linarith
    · rw [ite_eq_right hxΩ]
      exact (huc (by linarith : dist x p < δ)).trans (by linarith)

end CircleDomainRigidity

end

end OAI
